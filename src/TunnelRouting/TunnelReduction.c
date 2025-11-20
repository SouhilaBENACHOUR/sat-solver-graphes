#include "TunnelReduction.h"
#include "Z3Tools.h"
#include "stdio.h"

/**
 * @brief Creates the variable "x_{node,pos,stack_height}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param node A node.
 * @param pos The path position.
 * @param stack_height The highest cell occupied of the stack at that position.
 * @return Z3_ast
 */
Z3_ast tn_path_variable(Z3_context ctx, int node, int pos, int stack_height)
{
    char name[60];
    snprintf(name, 60, "node %d,pos %d, height %d", node, pos, stack_height);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Creates the variable "y_{pos,height,4}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_4_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "4 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Creates the variable "y_{pos,height,6}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_6_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "6 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Wrapper to have the correct size of the array representing the stack (correct cells of the stack will be from 0 to (get_stack_size(length)-1)).
 *
 * @param length The length of the sought path.
 * @return int
 */
int get_stack_size(int length)
{
    return length / 2 + 1;
}

/**
 * @brief Formule phi1 : Unicité du sommet et de la hauteur à chaque position.
 * Pour chaque position i, exactement un couple (sommet, hauteur) est choisi.
 *
 * @param ctx Le contexte Z3.
 * @param num_nodes Le nombre de sommets.
 * @param length La longueur du chemin.
 * @param stack_size La taille maximale de la pile.
 * @return Z3_ast La formule phi1.
 */
Z3_ast phi1_uniqueness(Z3_context ctx, int num_nodes, int length, int stack_size)
{
    Z3_ast formulas[length + 1];
    
    for (int pos = 0; pos <= length; pos++)
    {
        // Pour chaque position, on crée un tableau de toutes les variables possibles
        int count = 0;
        Z3_ast vars[num_nodes * stack_size];
        
        for (int node = 0; node < num_nodes; node++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                vars[count] = tn_path_variable(ctx, node, pos, height);
                count++;
            }
        }
        
        // Exactement une variable doit être vraie (fonction fournie)
        formulas[pos] = uniqueFormula(ctx, vars, count);
    }
    
    return Z3_mk_and(ctx, length + 1, formulas);
}

/**
 * @brief Formule phi2 : Conditions initiales et finales.
 * Le chemin commence à la source avec pile [4] de hauteur 0,
 * et se termine à la destination avec pile [4] de hauteur 0.
 *
 * @param ctx Le contexte Z3.
 * @param network Le réseau de tunnels.
 * @param length La longueur du chemin.
 * @return Z3_ast La formule phi2.
 */
Z3_ast phi2_initial_final(Z3_context ctx, const TunnelNetwork network, int length)
{
    int source = tn_get_initial(network);
    int dest = tn_get_final(network);
    
    // Condition initiale : x_{s,0,0} et y_{0,0,4} et non y_{0,0,6}
    Z3_ast initial[3];
    initial[0] = tn_path_variable(ctx, source, 0, 0);
    initial[1] = tn_4_variable(ctx, 0, 0);
    initial[2] = Z3_mk_not(ctx, tn_6_variable(ctx, 0, 0));
    Z3_ast init_formula = Z3_mk_and(ctx, 3, initial);
    
    // Condition finale : x_{d,length,0} et y_{length,0,4} et non y_{length,0,6}
    Z3_ast final[3];
    final[0] = tn_path_variable(ctx, dest, length, 0);
    final[1] = tn_4_variable(ctx, length, 0);
    final[2] = Z3_mk_not(ctx, tn_6_variable(ctx, length, 0));
    Z3_ast final_formula = Z3_mk_and(ctx, 3, final);
    
    Z3_ast result[2];
    result[0] = init_formula;
    result[1] = final_formula;
    
    return Z3_mk_and(ctx, 2, result);
}

/**
 * @brief Formule phi3 : Cohérence des hauteurs entre positions successives.
 * La hauteur peut changer de -1 (pop), 0 (transmit), ou +1 (push).
 *
 * @param ctx Le contexte Z3.
 * @param num_nodes Le nombre de sommets.
 * @param length La longueur du chemin.
 * @param stack_size La taille maximale de la pile.
 * @return Z3_ast La formule phi3.
 */
Z3_ast phi3_height_coherence(Z3_context ctx, int num_nodes, int length, int stack_size)
{
    int formula_count = 0;
    Z3_ast formulas[num_nodes * length * stack_size];
    
    for (int pos = 0; pos < length; pos++)
    {
        for (int node = 0; node < num_nodes; node++)
        {
            for (int h = 0; h < stack_size; h++)
            {
                // Si x_{node,pos,h} alors il existe un next_node et une hauteur h' adjacente
                Z3_ast condition = tn_path_variable(ctx, node, pos, h);
                
                // On construit les possibilités : h-1, h, h+1
                int possible_count = 0;
                Z3_ast possibilities[num_nodes * 3];
                
                for (int next_node = 0; next_node < num_nodes; next_node++)
                {
                    // Hauteur h-1 (pop)
                    if (h > 0)
                    {
                        possibilities[possible_count] = tn_path_variable(ctx, next_node, pos + 1, h - 1);
                        possible_count++;
                    }
                    
                    // Hauteur h (transmit)
                    possibilities[possible_count] = tn_path_variable(ctx, next_node, pos + 1, h);
                    possible_count++;
                    
                    // Hauteur h+1 (push)
                    if (h < stack_size - 1)
                    {
                        possibilities[possible_count] = tn_path_variable(ctx, next_node, pos + 1, h + 1);
                        possible_count++;
                    }
                }
                
                Z3_ast consequence = Z3_mk_or(ctx, possible_count, possibilities);
                formulas[formula_count] = Z3_mk_implies(ctx, condition, consequence);
                formula_count++;
            }
        }
    }
    
    return Z3_mk_and(ctx, formula_count, formulas);
}

/**
 * @brief Formule phi4 : Contenu de la pile bien défini.
 * Chaque cellule jusqu'à la hauteur contient soit 4 soit 6 (mais pas les deux).
 *
 * @param ctx Le contexte Z3.
 * @param num_nodes Le nombre de sommets.
 * @param length La longueur du chemin.
 * @param stack_size La taille maximale de la pile.
 * @return Z3_ast La formule phi4.
 */
Z3_ast phi4_stack_well_defined(Z3_context ctx, int num_nodes, int length, int stack_size)
{
    int formula_count = 0;
    Z3_ast formulas[num_nodes * (length + 1) * stack_size * stack_size];
    
    for (int pos = 0; pos <= length; pos++)
    {
        for (int node = 0; node < num_nodes; node++)
        {
            for (int h = 0; h < stack_size; h++)
            {
                Z3_ast condition = tn_path_variable(ctx, node, pos, h);
                
                // Pour chaque cellule k de 0 à h
                for (int k = 0; k <= h; k++)
                {
                    // (y_{pos,k,4} et non y_{pos,k,6}) ou (non y_{pos,k,4} et y_{pos,k,6})
                    Z3_ast y4 = tn_4_variable(ctx, pos, k);
                    Z3_ast y6 = tn_6_variable(ctx, pos, k);
                    
                    Z3_ast option1[2];
                    option1[0] = y4;
                    option1[1] = Z3_mk_not(ctx, y6);
                    
                    Z3_ast option2[2];
                    option2[0] = Z3_mk_not(ctx, y4);
                    option2[1] = y6;
                    
                    Z3_ast choices[2];
                    choices[0] = Z3_mk_and(ctx, 2, option1);
                    choices[1] = Z3_mk_and(ctx, 2, option2);
                    
                    Z3_ast consequence = Z3_mk_or(ctx, 2, choices);
                    formulas[formula_count] = Z3_mk_implies(ctx, condition, consequence);
                    formula_count++;
                }
            }
        }
    }
    
    return Z3_mk_and(ctx, formula_count, formulas);
}

/**
 * @brief Formule phi5_transmit : Capacité de transmission passive.
 * Si la hauteur reste h, le nœud doit pouvoir transmettre le protocole au sommet.
 *
 * @param ctx Le contexte Z3.
 * @param network Le réseau de tunnels.
 * @param length La longueur du chemin.
 * @param stack_size La taille maximale de la pile.
 * @return Z3_ast La formule phi5_transmit.
 */
Z3_ast phi5_transmit(Z3_context ctx, const TunnelNetwork network, int length, int stack_size)
{
    int num_nodes = tn_get_num_nodes(network);
    int formula_count = 0;
    Z3_ast formulas[num_nodes * num_nodes * length * stack_size];
    
    for (int pos = 0; pos < length; pos++)
    {
        for (int node = 0; node < num_nodes; node++)
        {
            for (int next_node = 0; next_node < num_nodes; next_node++)
            {
                for (int h = 0; h < stack_size; h++)
                {
                    // Si x_{node,pos,h} et x_{next_node,pos+1,h}
                    Z3_ast cond[2];
                    cond[0] = tn_path_variable(ctx, node, pos, h);
                    cond[1] = tn_path_variable(ctx, next_node, pos + 1, h);
                    Z3_ast condition = Z3_mk_and(ctx, 2, cond);
                    
                    // Alors (y_{pos,h,4} et node peut transmettre 4) ou (y_{pos,h,6} et node peut transmettre 6)
                    int poss_count = 0;
                    Z3_ast possibilities[2];
                    
                    if (tn_node_has_action(network, node, transmit_4))
                    {
                        possibilities[poss_count] = tn_4_variable(ctx, pos, h);
                        poss_count++;
                    }
                    
                    if (tn_node_has_action(network, node, transmit_6))
                    {
                        possibilities[poss_count] = tn_6_variable(ctx, pos, h);
                        poss_count++;
                    }
                    
                    if (poss_count > 0)
                    {
                        Z3_ast consequence = Z3_mk_or(ctx, poss_count, possibilities);
                        formulas[formula_count] = Z3_mk_implies(ctx, condition, consequence);
                        formula_count++;
                    }
                }
            }
        }
    }
    
    return Z3_mk_and(ctx, formula_count, formulas);
}

/**
 * @brief Formule phi5_push : Capacité d'encapsulation.
 * Si la hauteur passe de h à h+1, le nœud doit pouvoir faire push.
 *
 * @param ctx Le contexte Z3.
 * @param network Le réseau de tunnels.
 * @param length La longueur du chemin.
 * @param stack_size La taille maximale de la pile.
 * @return Z3_ast La formule phi5_push.
 */
Z3_ast phi5_push(Z3_context ctx, const TunnelNetwork network, int length, int stack_size)
{
    int num_nodes = tn_get_num_nodes(network);
    int formula_count = 0;
    Z3_ast formulas[num_nodes * num_nodes * length * stack_size * 4];
    
    for (int pos = 0; pos < length; pos++)
    {
        for (int node = 0; node < num_nodes; node++)
        {
            for (int next_node = 0; next_node < num_nodes; next_node++)
            {
                for (int h = 0; h < stack_size - 1; h++)
                {
                    // Si x_{node,pos,h} et x_{next_node,pos+1,h+1}
                    Z3_ast cond[2];
                    cond[0] = tn_path_variable(ctx, node, pos, h);
                    cond[1] = tn_path_variable(ctx, next_node, pos + 1, h + 1);
                    Z3_ast condition = Z3_mk_and(ctx, 2, cond);
                    
                    // On vérifie les 4 possibilités : push_4_4, push_4_6, push_6_4, push_6_6
                    int poss_count = 0;
                    Z3_ast possibilities[4];
                    
                    // push_4_4 : sommet actuel = 4, nouveau sommet = 4
                    if (tn_node_has_action(network, node, push_4_4))
                    {
                        Z3_ast parts[2];
                        parts[0] = tn_4_variable(ctx, pos, h);
                        parts[1] = tn_4_variable(ctx, pos + 1, h + 1);
                        possibilities[poss_count] = Z3_mk_and(ctx, 2, parts);
                        poss_count++;
                    }
                    
                    // push_4_6 : sommet actuel = 4, nouveau sommet = 6
                    if (tn_node_has_action(network, node, push_4_6))
                    {
                        Z3_ast parts[2];
                        parts[0] = tn_4_variable(ctx, pos, h);
                        parts[1] = tn_6_variable(ctx, pos + 1, h + 1);
                        possibilities[poss_count] = Z3_mk_and(ctx, 2, parts);
                        poss_count++;
                    }
                    
                    // push_6_4 : sommet actuel = 6, nouveau sommet = 4
                    if (tn_node_has_action(network, node, push_6_4))
                    {
                        Z3_ast parts[2];
                        parts[0] = tn_6_variable(ctx, pos, h);
                        parts[1] = tn_4_variable(ctx, pos + 1, h + 1);
                        possibilities[poss_count] = Z3_mk_and(ctx, 2, parts);
                        poss_count++;
                    }
                    
                    // push_6_6 : sommet actuel = 6, nouveau sommet = 6
                    if (tn_node_has_action(network, node, push_6_6))
                    {
                        Z3_ast parts[2];
                        parts[0] = tn_6_variable(ctx, pos, h);
                        parts[1] = tn_6_variable(ctx, pos + 1, h + 1);
                        possibilities[poss_count] = Z3_mk_and(ctx, 2, parts);
                        poss_count++;
                    }
                    
                    if (poss_count > 0)
                    {
                        Z3_ast consequence = Z3_mk_or(ctx, poss_count, possibilities);
                        formulas[formula_count] = Z3_mk_implies(ctx, condition, consequence);
                        formula_count++;
                    }
                }
            }
        }
    }
    
    return Z3_mk_and(ctx, formula_count, formulas);
}

/**
 * @brief Formule phi5_pop : Capacité de désencapsulation.
 * Si la hauteur passe de h à h-1, le nœud doit pouvoir faire pop.
 *
 * @param ctx Le contexte Z3.
 * @param network Le réseau de tunnels.
 * @param length La longueur du chemin.
 * @param stack_size La taille maximale de la pile.
 * @return Z3_ast La formule phi5_pop.
 */
Z3_ast phi5_pop(Z3_context ctx, const TunnelNetwork network, int length, int stack_size)
{
    int num_nodes = tn_get_num_nodes(network);
    int formula_count = 0;
    Z3_ast formulas[num_nodes * num_nodes * length * stack_size * 4];
    
    for (int pos = 0; pos < length; pos++)
    {
        for (int node = 0; node < num_nodes; node++)
        {
            for (int next_node = 0; next_node < num_nodes; next_node++)
            {
                for (int h = 1; h < stack_size; h++)
                {
                    // Si x_{node,pos,h} et x_{next_node,pos+1,h-1}
                    Z3_ast cond[2];
                    cond[0] = tn_path_variable(ctx, node, pos, h);
                    cond[1] = tn_path_variable(ctx, next_node, pos + 1, h - 1);
                    Z3_ast condition = Z3_mk_and(ctx, 2, cond);
                    
                    // On vérifie les 4 possibilités : pop_4_4, pop_4_6, pop_6_4, pop_6_6
                    int poss_count = 0;
                    Z3_ast possibilities[4];
                    
                    // pop_4_4 : sommet actuel = 4, cellule dessous = 4
                    if (tn_node_has_action(network, node, pop_4_4))
                    {
                        Z3_ast parts[2];
                        parts[0] = tn_4_variable(ctx, pos, h);
                        parts[1] = tn_4_variable(ctx, pos, h - 1);
                        possibilities[poss_count] = Z3_mk_and(ctx, 2, parts);
                        poss_count++;
                    }
                    
                    // pop_6_4 : sommet actuel = 6, cellule dessous = 4
                    if (tn_node_has_action(network, node, pop_6_4))
                    {
                        Z3_ast parts[2];
                        parts[0] = tn_6_variable(ctx, pos, h);
                        parts[1] = tn_4_variable(ctx, pos, h - 1);
                        possibilities[poss_count] = Z3_mk_and(ctx, 2, parts);
                        poss_count++;
                    }
                    
                    // pop_4_6 : sommet actuel = 4, cellule dessous = 6
                    if (tn_node_has_action(network, node, pop_4_6))
                    {
                        Z3_ast parts[2];
                        parts[0] = tn_4_variable(ctx, pos, h);
                        parts[1] = tn_6_variable(ctx, pos, h - 1);
                        possibilities[poss_count] = Z3_mk_and(ctx, 2, parts);
                        poss_count++;
                    }
                    
                    // pop_6_6 : sommet actuel = 6, cellule dessous = 6
                    if (tn_node_has_action(network, node, pop_6_6))
                    {
                        Z3_ast parts[2];
                        parts[0] = tn_6_variable(ctx, pos, h);
                        parts[1] = tn_6_variable(ctx, pos, h - 1);
                        possibilities[poss_count] = Z3_mk_and(ctx, 2, parts);
                        poss_count++;
                    }
                    
                    if (poss_count > 0)
                    {
                        Z3_ast consequence = Z3_mk_or(ctx, poss_count, possibilities);
                        formulas[formula_count] = Z3_mk_implies(ctx, condition, consequence);
                        formula_count++;
                    }
                }
            }
        }
    }
    
    return Z3_mk_and(ctx, formula_count, formulas);
}

/**
 * @brief Formule phi6 : Conservation de la pile.
 * Les cellules sous le sommet de pile ne changent pas entre positions successives.
 *
 * @param ctx Le contexte Z3.
 * @param num_nodes Le nombre de sommets.
 * @param length La longueur du chemin.
 * @param stack_size La taille maximale de la pile.
 * @return Z3_ast La formule phi6.
 */
Z3_ast phi6_stack_preservation(Z3_context ctx, int num_nodes, int length, int stack_size)
{
    int formula_count = 0;
    Z3_ast formulas[num_nodes * num_nodes * length * stack_size * stack_size * stack_size];
    
    for (int pos = 0; pos < length; pos++)
    {
        for (int node = 0; node < num_nodes; node++)
        {
            for (int next_node = 0; next_node < num_nodes; next_node++)
            {
                for (int h = 0; h < stack_size; h++)
                {
                    // On regarde les trois cas : h-1, h, h+1
                    for (int h_prime = (h > 0 ? h - 1 : 0); h_prime <= h + 1 && h_prime < stack_size; h_prime++)
                    {
                        // Si x_{node,pos,h} et x_{next_node,pos+1,h'}
                        Z3_ast cond[2];
                        cond[0] = tn_path_variable(ctx, node, pos, h);
                        cond[1] = tn_path_variable(ctx, next_node, pos + 1, h_prime);
                        Z3_ast condition = Z3_mk_and(ctx, 2, cond);
                        
                        // Pour chaque cellule k de 0 à min(h, h')-1
                        int min_h = (h < h_prime) ? h : h_prime;
                        if (min_h > 0)
                        {
                            int conseq_count = 0;
                            Z3_ast consequences[stack_size * 2];
                            
                            for (int k = 0; k < min_h; k++)
                            {
                                // y_{pos,k,4} <=> y_{pos+1,k,4}
                                Z3_ast equiv4 = Z3_mk_eq(ctx, tn_4_variable(ctx, pos, k), tn_4_variable(ctx, pos + 1, k));
                                consequences[conseq_count] = equiv4;
                                conseq_count++;
                                
                                // y_{pos,k,6} <=> y_{pos+1,k,6}
                                Z3_ast equiv6 = Z3_mk_eq(ctx, tn_6_variable(ctx, pos, k), tn_6_variable(ctx, pos + 1, k));
                                consequences[conseq_count] = equiv6;
                                conseq_count++;
                            }
                            
                            Z3_ast consequence = Z3_mk_and(ctx, conseq_count, consequences);
                            formulas[formula_count] = Z3_mk_implies(ctx, condition, consequence);
                            formula_count++;
                        }
                    }
                }
            }
        }
    }
    
    return Z3_mk_and(ctx, formula_count, formulas);
}

/**
 * @brief Formule phi7 : Contraintes de graphe.
 * Si le chemin passe de node à next_node, alors (node, next_node) doit être une arête.
 *
 * @param ctx Le contexte Z3.
 * @param network Le réseau de tunnels.
 * @param length La longueur du chemin.
 * @param stack_size La taille maximale de la pile.
 * @return Z3_ast La formule phi7.
 */
Z3_ast phi7_graph_edges(Z3_context ctx, const TunnelNetwork network, int length, int stack_size)
{
    int num_nodes = tn_get_num_nodes(network);
    int formula_count = 0;
    Z3_ast formulas[num_nodes * num_nodes * length * stack_size * stack_size];
    
    for (int pos = 0; pos < length; pos++)
    {
        for (int node = 0; node < num_nodes; node++)
        {
            for (int next_node = 0; next_node < num_nodes; next_node++)
            {
                // Si (node, next_node) n'est pas une arête
                if (!tn_is_edge(network, node, next_node))
                {
                    // Alors on interdit toutes les transitions de node à next_node
                    for (int h = 0; h < stack_size; h++)
                    {
                        for (int h_prime = 0; h_prime < stack_size; h_prime++)
                        {
                            // non x_{node,pos,h} ou non x_{next_node,pos+1,h'}
                            Z3_ast parts[2];
                            parts[0] = Z3_mk_not(ctx, tn_path_variable(ctx, node, pos, h));
                            parts[1] = Z3_mk_not(ctx, tn_path_variable(ctx, next_node, pos + 1, h_prime));
                            formulas[formula_count] = Z3_mk_or(ctx, 2, parts);
                            formula_count++;
                        }
                    }
                }
            }
        }
    }
    
    return Z3_mk_and(ctx, formula_count, formulas);
}

/**
 * @brief Formule phi8 : Chemin simple.
 * Un sommet n'apparaît qu'une seule fois dans le chemin.
 *
 * @param ctx Le contexte Z3.
 * @param num_nodes Le nombre de sommets.
 * @param length La longueur du chemin.
 * @param stack_size La taille maximale de la pile.
 * @return Z3_ast La formule phi8.
 */
Z3_ast phi8_simple_path(Z3_context ctx, int num_nodes, int length, int stack_size)
{
    int formula_count = 0;
    Z3_ast formulas[num_nodes * length * length * stack_size * stack_size];
    
    for (int node = 0; node < num_nodes; node++)
    {
        for (int pos1 = 0; pos1 <= length; pos1++)
        {
            for (int pos2 = pos1 + 1; pos2 <= length; pos2++)
            {
                // Le sommet node ne peut pas être à la fois en pos1 et pos2
                for (int h1 = 0; h1 < stack_size; h1++)
                {
                    for (int h2 = 0; h2 < stack_size; h2++)
                    {
                        // non x_{node,pos1,h1} ou non x_{node,pos2,h2}
                        Z3_ast parts[2];
                        parts[0] = Z3_mk_not(ctx, tn_path_variable(ctx, node, pos1, h1));
                        parts[1] = Z3_mk_not(ctx, tn_path_variable(ctx, node, pos2, h2));
                        formulas[formula_count] = Z3_mk_or(ctx, 2, parts);
                        formula_count++;
                    }
                }
            }
        }
    }
    
    return Z3_mk_and(ctx, formula_count, formulas);
}

Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);
    
    // On crée toutes les sous-formules
    Z3_ast phi1 = phi1_uniqueness(ctx, num_nodes, length, stack_size);
    Z3_ast phi2 = phi2_initial_final(ctx, network, length);
    Z3_ast phi3 = phi3_height_coherence(ctx, num_nodes, length, stack_size);
    Z3_ast phi4 = phi4_stack_well_defined(ctx, num_nodes, length, stack_size);
    
    // phi5 en trois parties
    Z3_ast phi5_t = phi5_transmit(ctx, network, length, stack_size);
    Z3_ast phi5_p = phi5_push(ctx, network, length, stack_size);
    Z3_ast phi5_d = phi5_pop(ctx, network, length, stack_size);
    Z3_ast phi5_parts[3] = {phi5_t, phi5_p, phi5_d};
    Z3_ast phi5 = Z3_mk_and(ctx, 3, phi5_parts);
    
    Z3_ast phi6 = phi6_stack_preservation(ctx, num_nodes, length, stack_size);
    Z3_ast phi7 = phi7_graph_edges(ctx, network, length, stack_size);
    Z3_ast phi8 = phi8_simple_path(ctx, num_nodes, length, stack_size);
    
    // Formule finale : conjonction de toutes les sous-formules
    Z3_ast all_formulas[8];
    all_formulas[0] = phi1;
    all_formulas[1] = phi2;
    all_formulas[2] = phi3;
    all_formulas[3] = phi4;
    all_formulas[4] = phi5;
    all_formulas[5] = phi6;
    all_formulas[6] = phi7;
    all_formulas[7] = phi8;
    
    return Z3_mk_and(ctx, 8, all_formulas);
}

void tn_get_path_from_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound, tn_step *path)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound; pos++)
    {
        int src = -1;
        int src_height = -1;
        int tgt = -1;
        int tgt_height = -1;
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
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
                action = transmit_4;
            else
                action = transmit_6;
        }
        else if (src_height == tgt_height - 1)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = push_4_4;
                else
                    action = push_4_6;
            }
            else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                action = push_6_4;
            else
                action = push_6_6;
        }
        else if (src_height == tgt_height + 1)
        {
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
                {
                    if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                        action = pop_4_4;
                    else
                        action = pop_6_4;
                }
                else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = pop_4_6;
                else
                    action = pop_6_6;
            }
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
    return;
}