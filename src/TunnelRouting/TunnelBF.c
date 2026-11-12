#include "TunnelBF.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

// Structure pour représenter l'état de la pile lors de la recherche
typedef struct {
 int *protocols; // Tableau des protocoles (4 ou 6)
 int height; // Hauteur actuelle (index du sommet)
 int capacity; // Taille max (liée à la borne)
} StackState;

/**
 * @brief Vérifie si une action est possible et met à jour la pile temporaire.
 * * @param network Le réseau.
 * @param u Nœud actuel (avant transition, source de l'arc mais pas de l'action).
 * @param v Nœud suivant (celui qui applique l'action).
 * @param current_stack La pile actuelle.
 * @param action L'action tentée par v.
 * @param next_stack Pointeur pour stocker la nouvelle pile résultante.
 * @return true si la transition est valide, false sinon.
 */
bool try_apply_action(TunnelNetwork network, int v, StackState *current_stack, 
 stack_action action, StackState *next_stack) 
{
 // Copie de l'état par défaut
 next_stack->height = current_stack->height;
 memcpy(next_stack->protocols, current_stack->protocols, (current_stack->height + 1) * sizeof(int));
 next_stack->capacity = current_stack->capacity;

 // Récupération des sommets pertinents
 int top = current_stack->protocols[current_stack->height];
 
 // Vérifier si le nœud v possède la capacité pour cette action
 if (!tn_node_has_action(network, v, action)) return false;

 // Logique selon le type d'action
 switch (action) {
 case transmit_4:
 if (top != 4) return false;
 return true; // Pile inchangée
 
 case transmit_6:
 if (top != 6) return false;
 return true; // Pile inchangée

 case push_4_4: // Old=4, New=4
 if (top != 4) return false;
 if (current_stack->height >= current_stack->capacity - 1) return false; // Stack overflow prevention
 next_stack->height++;
 next_stack->protocols[next_stack->height] = 4;
 return true;

 case push_4_6: // Old=4, New=6
 if (top != 4) return false;
 if (current_stack->height >= current_stack->capacity - 1) return false;
 next_stack->height++;
 next_stack->protocols[next_stack->height] = 6;
 return true;

 case push_6_4: // Old=6, New=4
 if (top != 6) return false;
 if (current_stack->height >= current_stack->capacity - 1) return false;
 next_stack->height++;
 next_stack->protocols[next_stack->height] = 4;
 return true;

 case push_6_6: // Old=6, New=6
 if (top != 6) return false;
 if (current_stack->height >= current_stack->capacity - 1) return false;
 next_stack->height++;
 next_stack->protocols[next_stack->height] = 6;
 return true;

 case pop_4_4: // New=4, Popped=4
 if (current_stack->height < 1) return false;
 if (top != 4) return false; // Popped
 if (current_stack->protocols[current_stack->height - 1] != 4) return false; // New Top
 next_stack->height--;
 return true;

 case pop_4_6: // New=4, Popped=6
 if (current_stack->height < 1) return false;
 if (top != 6) return false;
 if (current_stack->protocols[current_stack->height - 1] != 4) return false;
 next_stack->height--;
 return true;

 case pop_6_4: // New=6, Popped=4
 if (current_stack->height < 1) return false;
 if (top != 4) return false;
 if (current_stack->protocols[current_stack->height - 1] != 6) return false;
 next_stack->height--;
 return true;

 case pop_6_6: // New=6, Popped=6
 if (current_stack->height < 1) return false;
 if (top != 6) return false;
 if (current_stack->protocols[current_stack->height - 1] != 6) return false;
 next_stack->height--;
 return true;
 
 default: return false;
 }
}

/**
 * @brief Fonction récursive de recherche en profondeur (DFS).
 */
bool dfs_solve(TunnelNetwork network, int u, int target, int depth, int max_depth, 
 StackState *stack, bool *visited, tn_step *path) 
{
 // Cas de base : longueur atteinte
 if (depth == max_depth) {
 // Victoire si on est au nœud final, pile hauteur 0, contenu 4
 if (u == target && stack->height == 0 && stack->protocols[0] == 4) {
 return true;
 }
 return false;
 }

 int num_nodes = tn_get_num_nodes(network);
 StackState next_stack_state;
 next_stack_state.protocols = (int *)malloc(stack->capacity * sizeof(int));
 next_stack_state.capacity = stack->capacity;

 // Essayer tous les voisins v
 for (int v = 0; v < num_nodes; v++) {
 // 1. Arc existe ?
 if (!tn_is_edge(network, u, v)) continue;
 
 // 2. Simplicité : v déjà visité ?
 if (visited[v]) continue;

 // 3. Essayer toutes les actions possibles par v
 for (int act = 0; act < NumActions; act++) {
 if (try_apply_action(network, v, stack, (stack_action)act, &next_stack_state)) {
 
 // Enregistrer le pas
 path[depth] = tn_step_create((stack_action)act, u, v);
 visited[v] = true;

 // Appel récursif
 if (dfs_solve(network, v, target, depth + 1, max_depth, &next_stack_state, visited, path)) {
 free(next_stack_state.protocols);
 return true; // Trouvé !
 }

 // Backtrack
 visited[v] = false;
 }
 }
 }

 free(next_stack_state.protocols);
 return false;
}

int tn_brute_force(TunnelNetwork network, int bound, tn_step *path) 
{
 int num_nodes = tn_get_num_nodes(network);
 int initial = tn_get_initial(network);
 int final = tn_get_final(network);

 // Allocation pour le suivi des visites (Simplicité)
 bool *visited = (bool *)calloc(num_nodes, sizeof(bool));
 
 // Allocation initiale de la pile
 StackState stack;
 stack.capacity = bound + 2; // Marge de sécurité
 stack.protocols = (int *)malloc(stack.capacity * sizeof(int));
 stack.height = 0;
 stack.protocols[0] = 4; // État initial standard [4]

 // Recherche itérative par profondeur (pour trouver le plus court chemin)
 for (int len = 1; len <= bound; len++) {
 // Reset visites pour chaque longueur
 for(int i=0; i<num_nodes; i++) visited[i] = false;
 visited[initial] = true; // Le départ est visité

 if (dfs_solve(network, initial, final, 0, len, &stack, visited, path)) {
 // Nettoyage
 free(visited);
 free(stack.protocols);
 return len; // Retourne la longueur du chemin trouvé
 }
 }

 free(visited);
 free(stack.protocols);
 return -1; // Pas de solution trouvée
}