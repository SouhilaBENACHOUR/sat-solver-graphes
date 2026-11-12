#include "TunnelReduction.h"
#include "Z3Tools.h"
#include "stdio.h"
#include <stdlib.h>

/**
 * @brief Génère la variable booléenne x_{node,pos,stack_height} pour la réduction.
 */
Z3_ast tn_path_variable(Z3_context ctx, int node, int pos, int stack_height)
{
    char name[60];
    snprintf(name, 60, "node %d,pos %d, height %d", node, pos, stack_height);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Génère la variable y_{pos,height,4} représentant IPv4 dans la pile.
 */
Z3_ast tn_4_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "4 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Génère la variable y_{pos,height,6} représentant IPv6 dans la pile.
 */
Z3_ast tn_6_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "6 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Calcule la taille maximale requise pour représenter la pile.
 */
int get_stack_size(int length)
{
    return length / 2 + 1;
}

/**
 * @brief φ1 + φ2: Définit les états initiaux et terminaux du chemin
 */
Z3_ast tn_initial_final_constraints(Z3_context ctx, const TunnelNetwork network, int length)
{
    int initial = tn_get_initial(network);
    int final = tn_get_final(network);
   
    Z3_ast clauses[4];
    clauses[0] = tn_path_variable(ctx, initial, 0, 0);
    clauses[1] = tn_4_variable(ctx, 0, 0);
    clauses[2] = tn_path_variable(ctx, final, length, 0);
    clauses[3] = tn_4_variable(ctx, length, 0);
   
    return Z3_mk_and(ctx, 4, clauses);
}

/**
 * @brief φ3: Assure l'unicité de l'état (nœud, hauteur) à chaque position
 */
Z3_ast tn_unique_state_per_position(Z3_context ctx, const TunnelNetwork network, int length, int stack_size)
{
    int num_nodes = tn_get_num_nodes(network);
    Z3_ast *clauses = malloc((length + 1) * sizeof(Z3_ast));
   
    for (int pos = 0; pos <= length; pos++)
    {
        int num_vars = num_nodes * stack_size;
        Z3_ast *vars = malloc(num_vars * sizeof(Z3_ast));
        int idx = 0;
       
        for (int node = 0; node < num_nodes; node++)
            for (int height = 0; height < stack_size; height++)
                vars[idx++] = tn_path_variable(ctx, node, pos, height);
       
        clauses[pos] = uniqueFormula(ctx, vars, num_vars);
        free(vars);
    }
   
    Z3_ast result = Z3_mk_and(ctx, length + 1, clauses);
    free(clauses);
    return result;
}

/**
 * @brief φ4: Garantit l'absence de cycles en interdisant les nœuds répétés
 */
Z3_ast tn_simple_path_constraint(Z3_context ctx, const TunnelNetwork network, int length, int stack_size)
{
    int num_nodes = tn_get_num_nodes(network);
    Z3_ast *clauses = malloc(num_nodes * sizeof(Z3_ast));
   
    for (int node = 0; node < num_nodes; node++)
    {
        int num_vars = (length + 1) * stack_size;
        Z3_ast *vars = malloc(num_vars * sizeof(Z3_ast));
        int idx = 0;
       
        for (int pos = 0; pos <= length; pos++)
            for (int height = 0; height < stack_size; height++)
                vars[idx++] = tn_path_variable(ctx, node, pos, height);
       
        clauses[node] = at_most_formula(ctx, vars, num_vars);
        free(vars);
    }
   
    Z3_ast result = Z3_mk_and(ctx, num_nodes, clauses);
    free(clauses);
    return result;
}

/**
 * @brief φ5: Impose que seules les arêtes existantes peuvent être empruntées
 */
Z3_ast tn_edge_constraints(Z3_context ctx, const TunnelNetwork network, int length, int stack_size)
{
    int num_nodes = tn_get_num_nodes(network);
    int max_clauses = length * num_nodes * num_nodes * stack_size * stack_size;
    Z3_ast *clauses = malloc(max_clauses * sizeof(Z3_ast));
    int num_clauses = 0;
   
    for (int pos = 0; pos < length; pos++)
    {
        for (int node1 = 0; node1 < num_nodes; node1++)
        {
            for (int node2 = 0; node2 < num_nodes; node2++)
            {
                if (!tn_is_edge(network, node1, node2))
                {
                    for (int h1 = 0; h1 < stack_size; h1++)
                    {
                        for (int h2 = 0; h2 < stack_size; h2++)
                        {
                            Z3_ast antecedents[2];
                            antecedents[0] = Z3_mk_not(ctx, tn_path_variable(ctx, node1, pos, h1));
                            antecedents[1] = Z3_mk_not(ctx, tn_path_variable(ctx, node2, pos + 1, h2));
                            clauses[num_clauses++] = Z3_mk_or(ctx, 2, antecedents);
                        }
                    }
                }
            }
        }
    }
   
    Z3_ast result = Z3_mk_and(ctx, num_clauses, clauses);
    free(clauses);
    return result;
}

/**
 * @brief φ6: Empêche la coexistence de deux protocoles dans une même cellule
 */
Z3_ast tn_stack_cell_constraints(Z3_context ctx, int length, int stack_size)
{
    int num_clauses = (length + 1) * stack_size;
    Z3_ast *clauses = malloc(num_clauses * sizeof(Z3_ast));
    int idx = 0;
   
    for (int pos = 0; pos <= length; pos++)
    {
        for (int height = 0; height < stack_size; height++)
        {
            Z3_ast vars[2];
            vars[0] = tn_4_variable(ctx, pos, height);
            vars[1] = tn_6_variable(ctx, pos, height);
            clauses[idx++] = at_most_formula(ctx, vars, 2);
        }
    }
   
    Z3_ast result = Z3_mk_and(ctx, num_clauses, clauses);
    free(clauses);
    return result;
}

/**
 * @brief Construit une clause d'implication pour les transmissions : 
 * si on transmet, la pile demeure inchangée
 */
Z3_ast make_transmit_clause(Z3_context ctx, int node, int node2, int pos, int h, int protocol)
{
    Z3_ast *premises = malloc(3 * sizeof(Z3_ast));
    premises[0] = tn_path_variable(ctx, node, pos, h);
    premises[1] = tn_path_variable(ctx, node2, pos + 1, h);
    premises[2] = (protocol == 4) ? tn_4_variable(ctx, pos, h) : tn_6_variable(ctx, pos, h);
    Z3_ast antecedent = Z3_mk_and(ctx, 3, premises);
    free(premises);
   
    // Conservation complète du contenu de la pile
    Z3_ast *consequences = malloc((h + 1) * 2 * sizeof(Z3_ast));
    int idx = 0;
    for (int k = 0; k <= h; k++)
    {
        // IPv4: préservation entre positions
        consequences[idx++] = Z3_mk_or(ctx, 2, (Z3_ast[]){
            Z3_mk_not(ctx, tn_4_variable(ctx, pos, k)),
            tn_4_variable(ctx, pos + 1, k)
        });
        // IPv6: préservation entre positions
        consequences[idx++] = Z3_mk_or(ctx, 2, (Z3_ast[]){
            Z3_mk_not(ctx, tn_6_variable(ctx, pos, k)),
            tn_6_variable(ctx, pos + 1, k)
        });
    }
    Z3_ast consequent = Z3_mk_and(ctx, idx, consequences);
    free(consequences);
   
    return Z3_mk_or(ctx, 2, (Z3_ast[]){Z3_mk_not(ctx, antecedent), consequent});
}

/**
 * @brief φ7: Modélise les opérations de transmission qui n'altèrent pas la pile
 */
Z3_ast tn_transmit_constraints(Z3_context ctx, const TunnelNetwork network, int length, int stack_size)
{
    int num_nodes = tn_get_num_nodes(network);
    int max_clauses = length * num_nodes * num_nodes * stack_size * 2;
    Z3_ast *clauses = malloc(max_clauses * sizeof(Z3_ast));
    int num_clauses = 0;
   
    for (int pos = 0; pos < length; pos++)
    {
        for (int n1 = 0; n1 < num_nodes; n1++)
        {
            for (int n2 = 0; n2 < num_nodes; n2++)
            {
                if (!tn_is_edge(network, n1, n2))
                    continue;
               
                for (int h = 0; h < stack_size; h++)
                {
                    if (tn_node_has_action(network, n1, transmit_4))
                        clauses[num_clauses++] = make_transmit_clause(ctx, n1, n2, pos, h, 4);
                   
                    if (tn_node_has_action(network, n1, transmit_6))
                        clauses[num_clauses++] = make_transmit_clause(ctx, n1, n2, pos, h, 6);
                }
            }
        }
    }
   
    Z3_ast result = Z3_mk_and(ctx, num_clauses, clauses);
    free(clauses);
    return result;
}

/**
 * @brief φ8: Gère les encapsulations qui ajoutent un protocole au sommet
 */
Z3_ast tn_push_constraints(Z3_context ctx, const TunnelNetwork network, int length, int stack_size)
{
    int num_nodes = tn_get_num_nodes(network);
    int max_clauses = length * num_nodes * num_nodes * stack_size * 4;
    Z3_ast *clauses = malloc(max_clauses * sizeof(Z3_ast));
    int num_clauses = 0;
   
    stack_action actions[4] = {push_4_4, push_4_6, push_6_4, push_6_6};
    int from[4] = {4, 4, 6, 6};
    int to[4] = {4, 6, 4, 6};
   
    for (int pos = 0; pos < length; pos++)
    {
        for (int n1 = 0; n1 < num_nodes; n1++)
        {
            for (int n2 = 0; n2 < num_nodes; n2++)
            {
                if (!tn_is_edge(network, n1, n2))
                    continue;
               
                for (int h = 0; h < stack_size - 1; h++)
                {
                    for (int a = 0; a < 4; a++)
                    {
                        if (!tn_node_has_action(network, n1, actions[a]))
                            continue;
                       
                        // Conditions: nœud n1 à hauteur h avec protocole "from", transition vers n2 à h+1
                        Z3_ast premises[3];
                        premises[0] = tn_path_variable(ctx, n1, pos, h);
                        premises[1] = tn_path_variable(ctx, n2, pos + 1, h + 1);
                        premises[2] = (from[a] == 4) ? tn_4_variable(ctx, pos, h) : tn_6_variable(ctx, pos, h);
                        Z3_ast antecedent = Z3_mk_and(ctx, 3, premises);
                       
                        // Effets: conservation des couches basses, ajout du protocole "to" en haut
                        int num_consequences = (h + 1) * 2 + 1;
                        Z3_ast *consequences = malloc(num_consequences * sizeof(Z3_ast));
                        int idx = 0;
                        for (int k = 0; k <= h; k++)
                        {
                            consequences[idx++] = Z3_mk_or(ctx, 2, (Z3_ast[]){
                                Z3_mk_not(ctx, tn_4_variable(ctx, pos, k)),
                                tn_4_variable(ctx, pos + 1, k)
                            });
                            consequences[idx++] = Z3_mk_or(ctx, 2, (Z3_ast[]){
                                Z3_mk_not(ctx, tn_6_variable(ctx, pos, k)),
                                tn_6_variable(ctx, pos + 1, k)
                            });
                        }
                        consequences[idx++] = (to[a] == 4) ? tn_4_variable(ctx, pos + 1, h + 1) : tn_6_variable(ctx, pos + 1, h + 1);
                       
                        Z3_ast consequent = Z3_mk_and(ctx, idx, consequences);
                        free(consequences);
                       
                        clauses[num_clauses++] = Z3_mk_or(ctx, 2, (Z3_ast[]){
                            Z3_mk_not(ctx, antecedent), consequent
                        });
                    }
                }
            }
        }
    }
   
    Z3_ast result = Z3_mk_and(ctx, num_clauses, clauses);
    free(clauses);
    return result;
}

/**
 * @brief φ9: Traite les désencapsulations qui retirent le protocole supérieur
 */
Z3_ast tn_pop_constraints(Z3_context ctx, const TunnelNetwork network, int length, int stack_size)
{
    int num_nodes = tn_get_num_nodes(network);
    int max_clauses = length * num_nodes * num_nodes * stack_size * 4;
    Z3_ast *clauses = malloc(max_clauses * sizeof(Z3_ast));
    int num_clauses = 0;
   
    stack_action actions[4] = {pop_4_4, pop_4_6, pop_6_4, pop_6_6};
    int top[4] = {4, 6, 4, 6};
    int below[4] = {4, 4, 6, 6};
   
    for (int pos = 0; pos < length; pos++)
    {
        for (int n1 = 0; n1 < num_nodes; n1++)
        {
            for (int n2 = 0; n2 < num_nodes; n2++)
            {
                if (!tn_is_edge(network, n1, n2))
                    continue;
               
                for (int h = 1; h < stack_size; h++)
                {
                    for (int a = 0; a < 4; a++)
                    {
                        if (!tn_node_has_action(network, n1, actions[a]))
                            continue;
                       
                        // Conditions: nœud n1 à h avec top[a] au sommet et below[a] en dessous, vers n2 à h-1
                        Z3_ast premises[4];
                        premises[0] = tn_path_variable(ctx, n1, pos, h);
                        premises[1] = tn_path_variable(ctx, n2, pos + 1, h - 1);
                        premises[2] = (top[a] == 4) ? tn_4_variable(ctx, pos, h) : tn_6_variable(ctx, pos, h);
                        premises[3] = (below[a] == 4) ? tn_4_variable(ctx, pos, h - 1) : tn_6_variable(ctx, pos, h - 1);
                        Z3_ast antecedent = Z3_mk_and(ctx, 4, premises);
                       
                        // Effets: maintien des couches restantes après suppression du sommet
                        int num_consequences = h * 2;
                        Z3_ast *consequences = malloc(num_consequences * sizeof(Z3_ast));
                        int idx = 0;
                        for (int k = 0; k < h; k++)
                        {
                            consequences[idx++] = Z3_mk_or(ctx, 2, (Z3_ast[]){
                                Z3_mk_not(ctx, tn_4_variable(ctx, pos, k)),
                                tn_4_variable(ctx, pos + 1, k)
                            });
                            consequences[idx++] = Z3_mk_or(ctx, 2, (Z3_ast[]){
                                Z3_mk_not(ctx, tn_6_variable(ctx, pos, k)),
                                tn_6_variable(ctx, pos + 1, k)
                            });
                        }
                       
                        Z3_ast consequent = Z3_mk_and(ctx, idx, consequences);
                        free(consequences);
                       
                        clauses[num_clauses++] = Z3_mk_or(ctx, 2, (Z3_ast[]){
                            Z3_mk_not(ctx, antecedent), consequent
                        });
                    }
                }
            }
        }
    }
   
    Z3_ast result = Z3_mk_and(ctx, num_clauses, clauses);
    free(clauses);
    return result;
}

/**
 * @brief φ10: Vérifie la validité des actions selon les capacités des nœuds
 * et l'état de la pile, en s'assurant de l'existence d'un successeur approprié
 */
Z3_ast tn_node_action_validity(Z3_context ctx, const TunnelNetwork network, int length, int stack_size)
{
    int num_nodes = tn_get_num_nodes(network);
    int max_clauses = length * num_nodes * stack_size * 20;
    Z3_ast *clauses = malloc(max_clauses * sizeof(Z3_ast));
    int num_clauses = 0;
   
    for (int pos = 0; pos < length; pos++)
    {
        for (int node = 0; node < num_nodes; node++)
        {
            for (int h1 = 0; h1 < stack_size; h1++)
            {
                Z3_ast at_state = tn_path_variable(ctx, node, pos, h1);
               
                // Agrégation de toutes les actions possibles avec vérification du protocole et du successeur
                Z3_ast valid_conditions[100];
                int num_conditions = 0;
               
                // Actions TRANSMIT: nécessitent protocole compatible et successeur à même hauteur
                if (tn_node_has_action(network, node, transmit_4))
                {
                    for (int n2 = 0; n2 < num_nodes; n2++)
                    {
                        if (tn_is_edge(network, node, n2))
                        {
                            Z3_ast cond[2] = {
                                tn_4_variable(ctx, pos, h1),
                                tn_path_variable(ctx, n2, pos + 1, h1)
                            };
                            valid_conditions[num_conditions++] = Z3_mk_and(ctx, 2, cond);
                        }
                    }
                }
               
                if (tn_node_has_action(network, node, transmit_6))
                {
                    for (int n2 = 0; n2 < num_nodes; n2++)
                    {
                        if (tn_is_edge(network, node, n2))
                        {
                            Z3_ast cond[2] = {
                                tn_6_variable(ctx, pos, h1),
                                tn_path_variable(ctx, n2, pos + 1, h1)
                            };
                            valid_conditions[num_conditions++] = Z3_mk_and(ctx, 2, cond);
                        }
                    }
                }
               
                // Actions PUSH: requièrent protocole de base et successeur à h+1
                if (h1 < stack_size - 1)
                {
                    stack_action push_actions[4] = {push_4_4, push_4_6, push_6_4, push_6_6};
                    int from_proto[4] = {4, 4, 6, 6};
                   
                    for (int a = 0; a < 4; a++)
                    {
                        if (tn_node_has_action(network, node, push_actions[a]))
                        {
                            Z3_ast top_is = (from_proto[a] == 4) ?
                                            tn_4_variable(ctx, pos, h1) :
                                            tn_6_variable(ctx, pos, h1);
                           
                            for (int n2 = 0; n2 < num_nodes; n2++)
                            {
                                if (tn_is_edge(network, node, n2))
                                {
                                    Z3_ast cond[2] = {
                                        top_is,
                                        tn_path_variable(ctx, n2, pos + 1, h1 + 1)
                                    };
                                    valid_conditions[num_conditions++] = Z3_mk_and(ctx, 2, cond);
                                }
                            }
                        }
                    }
                }
               
                // Actions POP: exigent configuration correcte sommet/dessous et successeur à h-1
                if (h1 >= 1)
                {
                    stack_action pop_actions[4] = {pop_4_4, pop_4_6, pop_6_4, pop_6_6};
                    int top_proto[4] = {4, 6, 4, 6};
                    int below_proto[4] = {4, 4, 6, 6};
                   
                    for (int a = 0; a < 4; a++)
                    {
                        if (tn_node_has_action(network, node, pop_actions[a]))
                        {
                            Z3_ast top_is = (top_proto[a] == 4) ?
                                           tn_4_variable(ctx, pos, h1) :
                                           tn_6_variable(ctx, pos, h1);
                            Z3_ast below_is = (below_proto[a] == 4) ?
                                             tn_4_variable(ctx, pos, h1 - 1) :
                                             tn_6_variable(ctx, pos, h1 - 1);
                           
                            for (int n2 = 0; n2 < num_nodes; n2++)
                            {
                                if (tn_is_edge(network, node, n2))
                                {
                                    Z3_ast cond[3] = {
                                        top_is,
                                        below_is,
                                        tn_path_variable(ctx, n2, pos + 1, h1 - 1)
                                    };
                                    valid_conditions[num_conditions++] = Z3_mk_and(ctx, 3, cond);
                                }
                            }
                        }
                    }
                }
               
                if (num_conditions > 0)
                {
                    // Disjunction des conditions valides
                    Z3_ast at_least_one_valid = Z3_mk_or(ctx, num_conditions, valid_conditions);
                    clauses[num_clauses++] = Z3_mk_or(ctx, 2, (Z3_ast[]){
                        Z3_mk_not(ctx, at_state),
                        at_least_one_valid
                    });
                }
                else
                {
                    // État impossible: aucune transition valide disponible
                    clauses[num_clauses++] = Z3_mk_not(ctx, at_state);
                }
            }
        }
    }
   
    Z3_ast result = Z3_mk_and(ctx, num_clauses, clauses);
    free(clauses);
    return result;
}

/**
 * @brief Fonction principale de réduction : combine toutes les sous-formules
 */
Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length)
{
    int stack_size = get_stack_size(length);
   
    Z3_ast phi1_2 = tn_initial_final_constraints(ctx, network, length);
    Z3_ast phi3 = tn_unique_state_per_position(ctx, network, length, stack_size);
    Z3_ast phi4 = tn_simple_path_constraint(ctx, network, length, stack_size);
    Z3_ast phi5 = tn_edge_constraints(ctx, network, length, stack_size);
    Z3_ast phi6 = tn_stack_cell_constraints(ctx, length, stack_size);
    Z3_ast phi7 = tn_transmit_constraints(ctx, network, length, stack_size);
    Z3_ast phi8 = tn_push_constraints(ctx, network, length, stack_size);
    Z3_ast phi9 = tn_pop_constraints(ctx, network, length, stack_size);
    Z3_ast phi10 = tn_node_action_validity(ctx, network, length, stack_size);
   
    Z3_ast formulas[9] = {phi1_2, phi3, phi4, phi5, phi6, phi7, phi8, phi9, phi10};
    return Z3_mk_and(ctx, 9, formulas);
}

void tn_get_path_from_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound, tn_step *path)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound; pos++)
    {
        int src = -1, src_height = -1, tgt = -1, tgt_height = -1;
       
        for (int n = 0; n < num_nodes; n++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos, height)))
                {
                    src = n;
                    src_height = height;
                }
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos + 1, height)))
                {
                    tgt = n;
                    tgt_height = height;
                }
            }
        }
       
        int action = 0;
        if (src_height == tgt_height)
        {
            action = value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)) ? transmit_4 : transmit_6;
        }
        else if (src_height == tgt_height - 1)
        {
            bool src_is_4 = value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height));
            bool tgt_is_4 = value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height));
            if (src_is_4 && tgt_is_4) action = push_4_4;
            else if (src_is_4) action = push_4_6;
            else if (tgt_is_4) action = push_6_4;
            else action = push_6_6;
        }
        else if (src_height == tgt_height + 1)
        {
            bool src_is_4 = value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height));
            bool tgt_is_4 = value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height));
            if (src_is_4 && tgt_is_4) action = pop_4_4;
            else if (src_is_4) action = pop_6_4;
            else if (tgt_is_4) action = pop_4_6;
            else action = pop_6_6;
        }
       
        path[pos] = tn_step_create(action, src, tgt);
    }
}

void tn_print_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound + 1; pos++)
    {
        printf("At pos %d:\nState: ", pos);
        int num_seen = 0;
        for (int node = 0; node < num_nodes; node++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, node, pos, height)))
                {
                    printf("(%s,%d) ", tn_get_node_name(network, node), height);
                    num_seen++;
                }
            }
        }
        if (num_seen == 0)
            printf("No node at that position !\n");
        else
            printf("\n");
        if (num_seen > 1)
            printf("Several pair node,height!\n");
        printf("Stack: ");
        bool misdefined = false;
        bool above_top = false;
        for (int height = 0; height < stack_size; height++)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, height)))
            {
                if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
                {
                    printf("|X");
                    misdefined = true;
                }
                else
                {
                    printf("|4");
                    if (above_top)
                        misdefined = true;
                }
            }
            else if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
            {
                printf("|6");
                if (above_top)
                    misdefined = true;
            }
            else
            {
                printf("| ");
                above_top = true;
            }
        }
        printf("\n");
        if (misdefined)
            printf("Warning: ill-defined stack\n");
    }
}