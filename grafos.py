import heapq, math
from collections import deque
class Graph:
    def __init__(self, vertices, edges, direct = False):
        self.adj = [[] for _ in range(vertices)]
        for edge in edges:
            v1, v2 = edge[:2]
            w = edge[2] if len(edge) == 3 else 1 # Define o peso como 1 se não for especificado
            self.adj[v1].append((v2, w))
            if not direct:
                self.adj[v2].append((v1, w)) # Grafo não direcionado
class dfs(Graph):
    def path_rec(self, visited, e, f, size):
        visited[e] = True
        if e == f:
            return size
        for i, w in self.adj[e]:
            if not visited[i]:
                r = self.path_rec(visited, i, f, size+w)
                if r != None:
                    return r
    def path(self, e, f):
        visited = [False] * len(self.adj)
        return self.path_rec(visited, e, f, 0)
class bfs(Graph):
    def path_rec(self, visited, e, f, caminho):
        visited[e] = True
        for i, w in self.adj[e]:
            if i == f:
                return caminho + [i]
            if visited[i] == False:
                self.pilha.append( (visited + [], 
                                    i, 
                                    caminho + [i]))
    def path(self, e, f):
        self.pilha = [([False] * len(self.adj), 
                       e, 
                       [e])]
        while self.pilha:
            visited, i, caminho = self.pilha.pop()
            r = self.path_rec(visited, i, f, caminho)
            if r != None:
                return r
class Dijkstra(Graph):

    def path(self, e, f):
        V = len(self.adj)  
        dist = [float('inf')] * V
        dist[e] = 0
        pai = [None] * V

        pilha = [(0, e)] # ordenada

        while pilha:
            size, i = heapq.heappop(pilha)
            # # Encontra o índice do menor elemento (menor distância acumulada)
            # min_index = min(range(len(pilha)), key=lambda x: pilha[x][0])
            # # Remove o menor elemento da lista manualmente
            # size, i = pilha.pop(min_index)
            if i == f:
                j = i
                path = []
                while j is not None:
                    path.append(j)
                    j = pai[j]
                return path[::-1], dist[f]
            
            for j, w, in self.adj[i]:
                if size+w < dist[j]: # se vale a pena, aqui que é a função de condição
                    dist[j] = size+w
                    pai[j] = i
                    heapq.heappush(pilha, (size+w, j)) # atualiza j

        return None, float('inf')
class Tarjan(Graph):
    def __init__(self, vertices, edges, direct=True):
        super().__init__(vertices, edges, direct)
        self.index = 0
        self.stack = []
        self.on_stack = [False] * vertices
        self.indices = [-1] * vertices
        self.low_link = [-1] * vertices
        self.sccs = []

    def strongconnect(self, v):
        # Define o índice e o low-link do vértice
        self.indices[v] = self.index
        self.low_link[v] = self.index
        self.index += 1
        self.stack.append(v)
        self.on_stack[v] = True

        # Considera todos os vizinhos
        for (w, _) in self.adj[v]:
            if self.indices[w] == -1:  # Se o vizinho w não foi visitado
                self.strongconnect(w)
                self.low_link[v] = min(self.low_link[v], self.low_link[w])
            elif self.on_stack[w]:  # Se o vizinho w está na stack
                self.low_link[v] = min(self.low_link[v], self.indices[w])

        # Se v é uma raiz de SCC
        if self.low_link[v] == self.indices[v]:
            scc = []
            while True:
                w = self.stack.pop()
                self.on_stack[w] = False
                scc.append(w)
                if w == v:
                    break
            self.sccs.append(scc)

    def find_sccs(self):
        for v in range(len(self.adj)):
            if self.indices[v] == -1:
                self.strongconnect(v)
        return self.sccs

    def scc_to_graph(self):
        # Primeiro, identificamos todos os SCCs
        sccs = self.find_sccs()

        # Mapeia cada vértice ao SCC correspondente
        scc_map = {}
        for idx, scc in enumerate(sccs):
            for vertex in scc:
                scc_map[vertex] = idx

        # Lista para armazenar as arestas do novo grafo
        new_edges = []

        # Constrói as arestas do novo grafo baseado no SCC
        for v in range(len(self.adj)):
            for (w, weight) in self.adj[v]:
                if scc_map[v] != scc_map[w]:  # Se v e w pertencem a SCCs diferentes
                    new_edges.append((scc_map[v], scc_map[w], weight))

        # O novo grafo terá um número de vértices igual ao número de SCCs
        new_graph = Graph(len(sccs), new_edges, direct=True)

        return new_graph
class Dinic():
    def __init__(self, vertices, edges):
        self.vertices = vertices
        self.adj = [[] for _ in range(vertices)]
        self.direct = True
        for edge in edges:
            v1, v2 = edge[:2]
            w = edge[2] if len(edge) == 3 else 1  # Define o peso como 1 se não for especificado

            # Adiciona a aresta v1 -> v2
            self.adj[v1].append([v2, w, len(self.adj[v2])])  
            
            # Adiciona a aresta reversa v2 -> v1 com capacidade 0
            self.adj[v2].append([v1, 0, len(self.adj[v1]) - 1])
        self.level = [-1] * vertices

    def bfs_level_graph(self, source, sink):
        """Realiza BFS para construir o grafo de nível."""
        self.level = [-1] * len(self.adj)
        self.level[source] = 0
        queue = deque([source])

        while queue:
            u = queue.popleft()
            for v, capacity, rev_index in self.adj[u]:
                if self.level[v] < 0 and capacity > 0:  # Se não foi visitado e tem capacidade residual
                    self.level[v] = self.level[u] + 1
                    queue.append(v)

        return self.level[sink] != -1  # Retorna True se o sink for alcançável

    def dfs_blocking_flow(self, u, flow, sink, start):
        """Realiza DFS para encontrar fluxos bloqueantes no grafo de nível."""
        if u == sink:
            return flow
        
        total_flow = 0
        while start[u] < len(self.adj[u]):
            v, capacity, rev_index = self.adj[u][start[u]]
            if self.level[v] == self.level[u] + 1 and capacity > 0:  # Apenas considere arestas no grafo de nível
                pushed = self.dfs_blocking_flow(v, min(flow, capacity), sink, start)
                if pushed > 0:
                    # Diminui a capacidade residual da aresta
                    self.adj[u][start[u]][1] -= pushed
                    # Aumenta a capacidade residual da aresta reversa
                    self.adj[v][rev_index][1] += pushed
                    return pushed
            start[u] += 1

        return 0

    def max_flow(self, source, sink):
        """Calcula o fluxo máximo do grafo."""
        max_flow = 0
        while self.bfs_level_graph(source, sink):
            start = [0] * self.vertices
            flow = self.dfs_blocking_flow(source, float('inf'), sink, start)
            while flow:
                max_flow += flow
                flow = self.dfs_blocking_flow(source, float('inf'), sink, start)
        return max_flow


class Dijkstrapar(Graph):
    def path(self, e, f):
        V = len(self.adj)
        self.nadj = [[] for _ in range(V)]

        # Construir o grafo G2
        for u in range(V):
            for v1, w1 in self.adj[u]:
                for v2, w2 in self.adj[v1]:
                    if u != v2:  # Garante que não estamos formando um loop para o vértice original
                        self.nadj[u].append((v2, w1 + w2))

        self.adj = self.nadj  # Atualiza a lista de adjacência para G2

        dist = [float('inf')] * V
        dist[e] = 0
        pai = [None] * V

        pilha = [(0, e)]  # Usando heapq para a fila de prioridades

        while pilha:
            size, i = heapq.heappop(pilha)
            if i == f:
                path = []
                while i is not None:
                    path.append(i)
                    i = pai[i]
                return path[::-1], dist[f]

            for j, w in self.adj[i]:
                if size + w < dist[j]:  # se vale a pena
                    dist[j] = size + w
                    pai[j] = i
                    heapq.heappush(pilha, (dist[j], j))  # atualiza j

        return None, float('inf')
class dfsimposto(Graph):
    def path_rec(self, visited, e, size):
        visited[e] = True
        custo = self.imposto[e]
        for i, w in self.adj[e]:
            if not visited[i]:
                custo+=self.path_rec(visited, i, w)
        return math.ceil(size*custo/4)
    def path(self, e, f):
        visited = [False] * len(self.adj)
        self.imposto = []
        return self.path_rec(visited, e, 0)
import unittest
class TestGraphAlgorithms(unittest.TestCase):

    def setUp(self):
        # Configuração de um grafo menor e mais simples para testes rápidos
        self.vertices = 6
        self.edges = [
            (0, 1, 10), (0, 2, 10),
            (1, 2, 2), (1, 3, 4), (1, 4, 8),
            (2, 4, 9), 
            (3, 5, 9),
            (4, 3, 6), (4, 5, 10)
        ]
        self.graph_dfs = dfs(self.vertices, self.edges, direct=True)
        self.graph_bfs = bfs(self.vertices, self.edges, direct=True)
        self.graph_dijkstra = Dijkstra(self.vertices, self.edges, direct=True)
        self.graph_tarjan = Tarjan(self.vertices, self.edges, direct=True)
        self.graph_dinic = Dinic(self.vertices, self.edges)

    # def test_dfs_path(self):
    #     # Teste da função de caminho do DFS
    #     path = self.graph_dfs.path(0, 3)
    #     self.assertIsNotNone(path, "DFS não encontrou um caminho entre 0 e 3")
    #     #self.assertEqual(path, 9, "DFS encontrou um caminho com peso incorreto de 0 a 3")

    # def test_bfs_path(self):
    #     # Teste da função de caminho do BFS
    #     path = self.graph_bfs.path(0, 3)
    #     self.assertIsNotNone(path, "BFS não encontrou um caminho entre 0 e 3")
    #     self.assertEqual(path, [0, 1, 3], "BFS encontrou um caminho incorreto de 0 a 3")

    # def test_dijkstra_path(self):
    #     # Teste da função de caminho do Dijkstra
    #     path, distance = self.graph_dijkstra.path(0, 3)
    #     self.assertIsNotNone(path, "Dijkstra não encontrou um caminho entre 0 e 3")
    #     self.assertEqual(path, [0, 1, 3], "Dijkstra encontrou um caminho incorreto de 0 a 3")
    #     self.assertEqual(distance, 9, "Dijkstra encontrou uma distância incorreta de 0 a 3")

    # def test_tarjan_scc(self):
    #     # Teste da função de SCC do Tarjan
    #     sccs = self.graph_tarjan.find_sccs()
    #     expected_sccs = [[0, 2, 3], [1, 4]]
    #     self.assertEqual(len(sccs), len(expected_sccs), "Tarjan encontrou um número incorreto de SCCs")
    #     for scc in expected_sccs:
    #         self.assertIn(scc, sccs, f"Tarjan não encontrou o SCC esperado: {scc}")

    def test_dinic_max_flow(self):
        # Teste da função de fluxo máximo do Dinic
        max_flow = self.graph_dinic.max_flow(0, 5)
        self.assertEqual(max_flow, 19, "Dinic encontrou um fluxo máximo incorreto de 0 a 5")

if __name__ == "__main__":
    unittest.main()
