import 'package:flutter/material.dart';
import 'dart:collection';
import 'dart:math' as math;

void main() {
  runApp(const RegexToDFAApp());
}

class RegexToDFAApp extends StatelessWidget {
  const RegexToDFAApp({Key? key}) : super(key: key);

  @override
  Widget build(BuildContext context) {
    return MaterialApp(
      title: 'Regex to DFA Converter',
      theme: ThemeData(
        primarySwatch: Colors.blue,
        useMaterial3: true,
      ),
      home: const RegexConverterPage(),
    );
  }
}

class NFAState {
  final int id;
  Map<String, Set<int>> transitions = {};

  NFAState(this.id);
}

class NFA {
  int startState;
  Set<int> acceptStates;
  Map<int, NFAState> states;

  NFA(this.startState, this.acceptStates, this.states);
}

class DFAState {
  final String id;
  final Set<int> nfaStates;
  Map<String, String> transitions = {};

  DFAState(this.id, this.nfaStates);
}

class DFA {
  String startState;
  Set<String> acceptStates;
  Map<String, DFAState> states;
  Set<String> alphabet;

  DFA(this.startState, this.acceptStates, this.states, this.alphabet);
}

class RegexConverterPage extends StatefulWidget {
  const RegexConverterPage({Key? key}) : super(key: key);

  @override
  State<RegexConverterPage> createState() => _RegexConverterPageState();
}

class _RegexConverterPageState extends State<RegexConverterPage> with SingleTickerProviderStateMixin {
  final TextEditingController _testStringController = TextEditingController();
  late TabController _tabController;
  NFA? nfa;
  DFA? dfa;
  DFA? minimizedDFA;
  List<String> steps = [];
  String? simulationResult;
  List<Map<String, dynamic>> simulationSteps = [];
  int currentSimulationStep = -1;

  @override
  void initState() {
    super.initState();
    _tabController = TabController(length: 4, vsync: this);
    _convertRegex();
  }

  @override
  void dispose() {
    _tabController.dispose();
    _testStringController.dispose();
    super.dispose();
  }

  void _convertRegex() {
    setState(() {
      steps.clear();

      // Step 1: Thompson's Construction
      steps.add("=== STEP 1: THOMPSON'S CONSTRUCTION ===");
      nfa = _thompsonConstruction();
      steps.add("NFA created with ${nfa!.states.length} states");
      steps.add(_getNFATable());

      // Step 2: Subset Construction
      steps.add("\n=== STEP 2: SUBSET CONSTRUCTION (NFA to DFA) ===");
      dfa = _subsetConstruction(nfa!);
      steps.add("DFA created with ${dfa!.states.length} states");
      steps.add(_getDFATable(dfa!));

      // Step 3: DFA Minimization
      steps.add("\n=== STEP 3: DFA MINIMIZATION ===");
      minimizedDFA = _minimizeDFA(dfa!);
      steps.add("Minimized DFA has ${minimizedDFA!.states.length} states");
      steps.add(_getDFATable(minimizedDFA!));
    });
  }

  NFA _thompsonConstruction() {
    // For regex: (a + ab*b + ba*a)* (cb + bc*)a
    int stateCounter = 0;
    Map<int, NFAState> allStates = {};

    NFAState createState() {
      var state = NFAState(stateCounter++);
      allStates[state.id] = state;
      return state;
    }

    void addTransition(NFAState from, String symbol, NFAState to) {
      if (!from.transitions.containsKey(symbol)) {
        from.transitions[symbol] = {};
      }
      from.transitions[symbol]!.add(to.id);
    }

    // Build: a
    var a_start = createState();
    var a_end = createState();
    addTransition(a_start, 'a', a_end);

    // Build: ab*b (which is a, b*, b in sequence)
    var ab_start = createState();
    var ab_a = createState();
    var ab_bstar_start = createState();
    var ab_bstar_end = createState();
    var ab_b = createState();
    var ab_end = createState();

    addTransition(ab_start, 'a', ab_a);
    addTransition(ab_a, 'ε', ab_bstar_start);
    addTransition(ab_bstar_start, 'ε', ab_bstar_end);
    addTransition(ab_bstar_start, 'b', ab_bstar_start);
    addTransition(ab_bstar_end, 'ε', ab_b);
    addTransition(ab_b, 'b', ab_end);

    // Build: ba*a
    var ba_start = createState();
    var ba_b = createState();
    var ba_astar_start = createState();
    var ba_astar_end = createState();
    var ba_a = createState();
    var ba_end = createState();

    addTransition(ba_start, 'b', ba_b);
    addTransition(ba_b, 'ε', ba_astar_start);
    addTransition(ba_astar_start, 'ε', ba_astar_end);
    addTransition(ba_astar_start, 'a', ba_astar_start);
    addTransition(ba_astar_end, 'ε', ba_a);
    addTransition(ba_a, 'a', ba_end);

    // Union: (a + ab*b + ba*a)
    var union_start = createState();
    var union_end = createState();
    addTransition(union_start, 'ε', a_start);
    addTransition(union_start, 'ε', ab_start);
    addTransition(union_start, 'ε', ba_start);
    addTransition(a_end, 'ε', union_end);
    addTransition(ab_end, 'ε', union_end);
    addTransition(ba_end, 'ε', union_end);

    // Kleene star: (a + ab*b + ba*a)*
    var star_start = createState();
    var star_end = createState();
    addTransition(star_start, 'ε', union_start);
    addTransition(star_start, 'ε', star_end);
    addTransition(union_end, 'ε', union_start);
    addTransition(union_end, 'ε', star_end);

    // Build: cb
    var cb_start = createState();
    var cb_c = createState();
    var cb_end = createState();
    addTransition(cb_start, 'c', cb_c);
    addTransition(cb_c, 'b', cb_end);

    // Build: bc*
    var bc_start = createState();
    var bc_b = createState();
    var bc_cstar_start = createState();
    var bc_end = createState();
    addTransition(bc_start, 'b', bc_b);
    addTransition(bc_b, 'ε', bc_cstar_start);
    addTransition(bc_cstar_start, 'ε', bc_end);
    addTransition(bc_cstar_start, 'c', bc_cstar_start);

    // Union: (cb + bc*)
    var union2_start = createState();
    var union2_end = createState();
    addTransition(union2_start, 'ε', cb_start);
    addTransition(union2_start, 'ε', bc_start);
    addTransition(cb_end, 'ε', union2_end);
    addTransition(bc_end, 'ε', union2_end);

    // Final: (cb + bc*)a
    var final_a = createState();
    var final_end = createState();
    addTransition(union2_end, 'ε', final_a);
    addTransition(final_a, 'a', final_end);

    // Concatenate: (a + ab*b + ba*a)* (cb + bc*)a
    addTransition(star_end, 'ε', union2_start);

    return NFA(star_start.id, {final_end.id}, allStates);
  }

  Set<int> _epsilonClosure(Set<int> states, NFA nfa) {
    Set<int> closure = Set.from(states);
    Queue<int> queue = Queue.from(states);

    while (queue.isNotEmpty) {
      int current = queue.removeFirst();
      if (nfa.states[current]?.transitions.containsKey('ε') ?? false) {
        for (int next in nfa.states[current]!.transitions['ε']!) {
          if (!closure.contains(next)) {
            closure.add(next);
            queue.add(next);
          }
        }
      }
    }
    return closure;
  }

  DFA _subsetConstruction(NFA nfa) {
    Set<String> alphabet = {'a', 'b', 'c'};
    Map<String, DFAState> dfaStates = {};
    Queue<Set<int>> unprocessed = Queue();
    Map<String, Set<int>> stateMap = {};

    Set<int> startClosure = _epsilonClosure({nfa.startState}, nfa);
    String startId = 'q0';
    stateMap[startId] = startClosure;
    dfaStates[startId] = DFAState(startId, startClosure);
    unprocessed.add(startClosure);

    int stateIdCounter = 1;

    while (unprocessed.isNotEmpty) {
      Set<int> current = unprocessed.removeFirst();
      String currentId = stateMap.entries
          .firstWhere((e) => e.value.difference(current).isEmpty &&
          current.difference(e.value).isEmpty)
          .key;

      for (String symbol in alphabet) {
        Set<int> nextStates = {};
        for (int state in current) {
          if (nfa.states[state]?.transitions.containsKey(symbol) ?? false) {
            nextStates.addAll(nfa.states[state]!.transitions[symbol]!);
          }
        }

        if (nextStates.isEmpty) continue;

        Set<int> nextClosure = _epsilonClosure(nextStates, nfa);

        String? nextId = stateMap.entries
            .where((e) => e.value.difference(nextClosure).isEmpty &&
            nextClosure.difference(e.value).isEmpty)
            .map((e) => e.key)
            .firstOrNull;

        if (nextId == null) {
          nextId = 'q$stateIdCounter';
          stateIdCounter++;
          stateMap[nextId] = nextClosure;
          dfaStates[nextId] = DFAState(nextId, nextClosure);
          unprocessed.add(nextClosure);
        }

        dfaStates[currentId]!.transitions[symbol] = nextId;
      }
    }

    Set<String> acceptStates = {};
    for (var entry in dfaStates.entries) {
      if (entry.value.nfaStates.intersection(nfa.acceptStates).isNotEmpty) {
        acceptStates.add(entry.key);
      }
    }

    return DFA(startId, acceptStates, dfaStates, alphabet);
  }

  DFA _minimizeDFA(DFA dfa) {
    // Table-filling algorithm
    List<String> stateList = dfa.states.keys.toList();
    int n = stateList.length;

    // Initialize distinguishability table
    Map<String, Map<String, bool>> distinguishable = {};
    for (int i = 0; i < n; i++) {
      distinguishable[stateList[i]] = {};
      for (int j = i + 1; j < n; j++) {
        bool isAcceptI = dfa.acceptStates.contains(stateList[i]);
        bool isAcceptJ = dfa.acceptStates.contains(stateList[j]);
        distinguishable[stateList[i]]![stateList[j]] = isAcceptI != isAcceptJ;
      }
    }

    // Iterate until no more changes
    bool changed = true;
    while (changed) {
      changed = false;
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          if (distinguishable[stateList[i]]![stateList[j]]!) continue;

          for (String symbol in dfa.alphabet) {
            String? nextI = dfa.states[stateList[i]]!.transitions[symbol];
            String? nextJ = dfa.states[stateList[j]]!.transitions[symbol];

            if (nextI == null || nextJ == null) {
              if (nextI != nextJ) {
                distinguishable[stateList[i]]![stateList[j]] = true;
                changed = true;
                break;
              }
            } else if (nextI != nextJ) {
              String minState = nextI.compareTo(nextJ) < 0 ? nextI : nextJ;
              String maxState = nextI.compareTo(nextJ) < 0 ? nextJ : nextI;

              if (distinguishable[minState]?[maxState] ?? false) {
                distinguishable[stateList[i]]![stateList[j]] = true;
                changed = true;
                break;
              }
            }
          }
        }
      }
    }

    // Merge equivalent states
    Map<String, String> representative = {};
    for (String state in stateList) {
      representative[state] = state;
    }

    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (!(distinguishable[stateList[i]]![stateList[j]]!)) {
          String rep = representative[stateList[i]]!;
          representative[stateList[j]] = rep;
        }
      }
    }

    // Build minimized DFA
    Map<String, DFAState> newStates = {};
    Set<String> processedReps = {};

    for (String state in stateList) {
      String rep = representative[state]!;
      if (processedReps.contains(rep)) continue;
      processedReps.add(rep);

      newStates[rep] = DFAState(rep, {});
      for (String symbol in dfa.alphabet) {
        String? next = dfa.states[state]!.transitions[symbol];
        if (next != null) {
          newStates[rep]!.transitions[symbol] = representative[next]!;
        }
      }
    }

    String newStart = representative[dfa.startState]!;
    Set<String> newAccept = dfa.acceptStates
        .map((s) => representative[s]!)
        .toSet();

    return DFA(newStart, newAccept, newStates, dfa.alphabet);
  }

  String _getNFATable() {
    if (nfa == null) return '';

    StringBuffer sb = StringBuffer();
    sb.writeln('\nNFA Transition Table:');
    sb.writeln('State | ε | a | b | c');
    sb.writeln('------|---|---|---|---');

    for (int stateId in nfa!.states.keys.toList()..sort()) {
      String marker = '';
      if (stateId == nfa!.startState) marker = '→';
      if (nfa!.acceptStates.contains(stateId)) marker += '*';

      sb.write('$marker$stateId | ');

      for (String symbol in ['ε', 'a', 'b', 'c']) {
        if (nfa!.states[stateId]!.transitions.containsKey(symbol)) {
          sb.write('{${nfa!.states[stateId]!.transitions[symbol]!.join(',')}}');
        } else {
          sb.write('∅');
        }
        sb.write(' | ');
      }
      sb.writeln();
    }

    return sb.toString();
  }

  String _getDFATable(DFA dfa) {
    StringBuffer sb = StringBuffer();
    sb.writeln('\nDFA Transition Table:');
    sb.writeln('State | a | b | c');
    sb.writeln('------|---|---|---');

    for (String stateId in dfa.states.keys.toList()..sort()) {
      String marker = '';
      if (stateId == dfa.startState) marker = '→';
      if (dfa.acceptStates.contains(stateId)) marker += '*';

      sb.write('$marker$stateId | ');

      for (String symbol in ['a', 'b', 'c']) {
        String? next = dfa.states[stateId]!.transitions[symbol];
        sb.write(next ?? '∅');
        sb.write(' | ');
      }
      sb.writeln();
    }

    return sb.toString();
  }

  void _simulateString(String input) {
    if (minimizedDFA == null) return;

    setState(() {
      simulationSteps.clear();
      currentSimulationStep = 0;
      String currentState = minimizedDFA!.startState;

      simulationSteps.add({
        'step': 0,
        'state': currentState,
        'remaining': input,
        'symbol': 'START'
      });

      for (int i = 0; i < input.length; i++) {
        String symbol = input[i];
        String? nextState = minimizedDFA!.states[currentState]?.transitions[symbol];

        if (nextState == null) {
          simulationResult = 'REJECTED: No transition for "$symbol" from state $currentState';
          return;
        }

        currentState = nextState;
        simulationSteps.add({
          'step': i + 1,
          'state': currentState,
          'remaining': input.substring(i + 1),
          'symbol': symbol
        });
      }

      if (minimizedDFA!.acceptStates.contains(currentState)) {
        simulationResult = 'ACCEPTED: String accepted in final state $currentState';
      } else {
        simulationResult = 'REJECTED: Ended in non-accept state $currentState';
      }
    });
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        title: const Text('Regex to DFA Converter'),
        backgroundColor: Theme.of(context).colorScheme.inversePrimary,
        bottom: TabBar(
          controller: _tabController,
          tabs: const [
            Tab(text: 'Overview'),
            Tab(text: 'NFA Diagram'),
            Tab(text: 'DFA Diagram'),
            Tab(text: 'Simulator'),
          ],
        ),
      ),
      body: TabBarView(
        controller: _tabController,
        children: [
          _buildOverviewTab(),
          _buildNFADiagramTab(),
          _buildDFADiagramTab(),
          _buildSimulatorTab(),
        ],
      ),
    );
  }

  Widget _buildOverviewTab() {
    return SingleChildScrollView(
      padding: const EdgeInsets.all(16),
      child: Column(
        crossAxisAlignment: CrossAxisAlignment.start,
        children: [
          Card(
            child: Padding(
              padding: const EdgeInsets.all(16),
              child: Column(
                crossAxisAlignment: CrossAxisAlignment.start,
                children: [
                  Text(
                    'Regular Expression:',
                    style: Theme.of(context).textTheme.titleLarge,
                  ),
                  const SizedBox(height: 8),
                  Text(
                    '(a + ab*b + ba*a)* (cb + bc*)a',
                    style: Theme.of(context).textTheme.headlineSmall?.copyWith(
                      fontFamily: 'monospace',
                      color: Colors.blue,
                    ),
                  ),
                ],
              ),
            ),
          ),
          const SizedBox(height: 20),

          Card(
            child: Padding(
              padding: const EdgeInsets.all(16),
              child: Column(
                crossAxisAlignment: CrossAxisAlignment.start,
                children: [
                  Text(
                    'Conversion Steps:',
                    style: Theme.of(context).textTheme.titleLarge,
                  ),
                  const SizedBox(height: 12),
                  Container(
                    padding: const EdgeInsets.all(12),
                    decoration: BoxDecoration(
                      color: Colors.grey[100],
                      borderRadius: BorderRadius.circular(8),
                    ),
                    child: SelectableText(
                      steps.join('\n'),
                      style: const TextStyle(
                        fontFamily: 'monospace',
                        fontSize: 12,
                      ),
                    ),
                  ),
                ],
              ),
            ),
          ),
        ],
      ),
    );
  }

  Widget _buildNFADiagramTab() {
    return Column(
      children: [
        Padding(
          padding: const EdgeInsets.all(16),
          child: Text(
            'NFA State Diagram',
            style: Theme.of(context).textTheme.titleLarge,
          ),
        ),
        Expanded(
          child: nfa != null
              ? InteractiveViewer(
            boundaryMargin: const EdgeInsets.all(100),
            minScale: 0.1,
            maxScale: 4.0,
            child: CustomPaint(
              size: Size.infinite,
              painter: NFADiagramPainter(nfa!),
            ),
          )
              : const Center(child: CircularProgressIndicator()),
        ),
      ],
    );
  }

  Widget _buildDFADiagramTab() {
    return Column(
      children: [
        Padding(
          padding: const EdgeInsets.all(16),
          child: Text(
            'Minimized DFA State Diagram',
            style: Theme.of(context).textTheme.titleLarge,
          ),
        ),
        Expanded(
          child: minimizedDFA != null
              ? InteractiveViewer(
            boundaryMargin: const EdgeInsets.all(100),
            minScale: 0.1,
            maxScale: 4.0,
            child: CustomPaint(
              size: Size.infinite,
              painter: DFADiagramPainter(
                minimizedDFA!,
                currentState: simulationSteps.isNotEmpty && currentSimulationStep >= 0
                    ? simulationSteps[currentSimulationStep]['state']
                    : null,
              ),
            ),
          )
              : const Center(child: CircularProgressIndicator()),
        ),
      ],
    );
  }

  Widget _buildSimulatorTab() {
    return SingleChildScrollView(
      padding: const EdgeInsets.all(16),
      child: Column(
        crossAxisAlignment: CrossAxisAlignment.start,
        children: [
          Card(
            child: Padding(
              padding: const EdgeInsets.all(16),
              child: Column(
                crossAxisAlignment: CrossAxisAlignment.start,
                children: [
                  Text(
                    'regex = (a+ab*b+ba*a)*(cb+bc*)a)'
                  ),
                  Text(
                    'String Simulator:',
                    style: Theme.of(context).textTheme.titleLarge,
                  ),
                  const SizedBox(height: 12),
                  TextField(
                    controller: _testStringController,
                    decoration: const InputDecoration(
                      labelText: 'Enter test string',
                      hintText: 'e.g., abba, cba, bca',
                      border: OutlineInputBorder(),
                    ),
                  ),
                  const SizedBox(height: 12),
                  Row(
                    children: [
                      ElevatedButton(
                        onPressed: () {
                          _simulateString(_testStringController.text);
                        },
                        child: const Text('Simulate'),
                      ),
                      const SizedBox(width: 12),
                      if (simulationSteps.isNotEmpty) ...[
                        IconButton(
                          onPressed: currentSimulationStep > 0
                              ? () {
                            setState(() {
                              currentSimulationStep--;
                            });
                          }
                              : null,
                          icon: const Icon(Icons.arrow_back),
                        ),
                        Text('Step ${currentSimulationStep + 1}/${simulationSteps.length}'),
                        IconButton(
                          onPressed: currentSimulationStep < simulationSteps.length - 1
                              ? () {
                            setState(() {
                              currentSimulationStep++;
                            });
                          }
                              : null,
                          icon: const Icon(Icons.arrow_forward),
                        ),
                      ],
                    ],
                  ),
                  if (simulationSteps.isNotEmpty) ...[
                    const SizedBox(height: 16),
                    Text(
                      'Step-by-Step Simulation:',
                      style: Theme.of(context).textTheme.titleMedium,
                    ),
                    const SizedBox(height: 8),
                    ...simulationSteps.asMap().entries.map((entry) {
                      int idx = entry.key;
                      var step = entry.value;
                      bool isCurrentStep = idx == currentSimulationStep;

                      return Container(
                        padding: const EdgeInsets.symmetric(vertical: 4, horizontal: 8),
                        margin: const EdgeInsets.symmetric(vertical: 2),
                        decoration: BoxDecoration(
                          color: isCurrentStep ? Colors.blue[100] : Colors.transparent,
                          borderRadius: BorderRadius.circular(4),
                        ),
                        child: Text(
                          'Step ${step['step']}: State=${step['state']}, '
                              'Read="${step['symbol']}", Remaining="${step['remaining']}"',
                          style: TextStyle(
                            fontFamily: 'monospace',
                            fontWeight: isCurrentStep ? FontWeight.bold : FontWeight.normal,
                          ),
                        ),
                      );
                    }),
                    const SizedBox(height: 12),
                    Container(
                      padding: const EdgeInsets.all(12),
                      decoration: BoxDecoration(
                        color: simulationResult!.startsWith('ACCEPTED')
                            ? Colors.green[100]
                            : Colors.red[100],
                        borderRadius: BorderRadius.circular(8),
                      ),
                      child: Text(
                        simulationResult!,
                        style: TextStyle(
                          fontWeight: FontWeight.bold,
                          color: simulationResult!.startsWith('ACCEPTED')
                              ? Colors.green[900]
                              : Colors.red[900],
                        ),
                      ),
                    ),
                  ],
                ],
              ),
            ),
          ),
        ],
      ),
    );
  }
}

class NFADiagramPainter extends CustomPainter {
  final NFA nfa;

  NFADiagramPainter(this.nfa);

  @override
  void paint(Canvas canvas, Size size) {
    final paint = Paint()
      ..color = Colors.black
      ..strokeWidth = 2
      ..style = PaintingStyle.stroke;

    final arrowPaint = Paint()
      ..color = Colors.black
      ..strokeWidth = 2
      ..style = PaintingStyle.fill;

    final textPainter = TextPainter(
      textDirection: TextDirection.ltr,
    );

    // Calculate positions for states in a circular layout
    Map<int, Offset> positions = {};
    List<int> stateIds = nfa.states.keys.toList()..sort();

    // Use a grid layout for better visibility with many states
    int cols = math.sqrt(stateIds.length).ceil();
    int rows = (stateIds.length / cols).ceil();
    double cellWidth = size.width / (cols + 1);
    double cellHeight = size.height / (rows + 1);

    for (int i = 0; i < stateIds.length; i++) {
      int row = i ~/ cols;
      int col = i % cols;
      positions[stateIds[i]] = Offset(
        cellWidth * (col + 1),
        cellHeight * (row + 1),
      );
    }

    // Draw transitions
    for (var stateId in stateIds) {
      var state = nfa.states[stateId]!;
      var fromPos = positions[stateId]!;

      Map<int, List<String>> transitionsByTarget = {};

      for (var entry in state.transitions.entries) {
        String symbol = entry.key;
        for (int target in entry.value) {
          if (!transitionsByTarget.containsKey(target)) {
            transitionsByTarget[target] = [];
          }
          transitionsByTarget[target]!.add(symbol);
        }
      }

      for (var entry in transitionsByTarget.entries) {
        int targetId = entry.key;
        List<String> symbols = entry.value;
        var toPos = positions[targetId]!;

        if (stateId == targetId) {
          // Self-loop
          _drawSelfLoop(canvas, fromPos, symbols.join(','), textPainter);
        } else {
          _drawArrow(canvas, fromPos, toPos, paint, arrowPaint, symbols.join(','), textPainter);
        }
      }
    }

    // Draw states
    for (var stateId in stateIds) {
      var pos = positions[stateId]!;
      bool isStart = stateId == nfa.startState;
      bool isAccept = nfa.acceptStates.contains(stateId);

      _drawState(canvas, pos, stateId.toString(), isStart, isAccept, textPainter, false);
    }
  }

  void _drawState(Canvas canvas, Offset pos, String label, bool isStart, bool isAccept, TextPainter textPainter, bool isCurrent) {
    final paint = Paint()
      ..color = isStart ? Colors.green : (isCurrent ? Colors.orange : Colors.white)
      ..style = PaintingStyle.fill;

    final borderPaint = Paint()
      ..color = Colors.black
      ..strokeWidth = 2
      ..style = PaintingStyle.stroke;

    const double radius = 25;

    // Draw outer circle for accept states
    if (isAccept) {
      canvas.drawCircle(pos, radius + 5, borderPaint);
    }

    // Draw main circle
    canvas.drawCircle(pos, radius, paint);
    canvas.drawCircle(pos, radius, borderPaint);

    // Draw label
    textPainter.text = TextSpan(
      text: label,
      style: const TextStyle(color: Colors.black, fontSize: 14, fontWeight: FontWeight.bold),
    );
    textPainter.layout();
    textPainter.paint(
      canvas,
      Offset(pos.dx - textPainter.width / 2, pos.dy - textPainter.height / 2),
    );

    // Draw start arrow
    if (isStart) {
      final startArrowStart = Offset(pos.dx - radius - 40, pos.dy);
      final startArrowEnd = Offset(pos.dx - radius - 5, pos.dy);
      canvas.drawLine(startArrowStart, startArrowEnd, borderPaint);
      _drawArrowHead(canvas, startArrowStart, startArrowEnd, borderPaint);
    }
  }

  void _drawArrow(Canvas canvas, Offset from, Offset to, Paint linePaint, Paint arrowPaint, String label, TextPainter textPainter) {
    const double radius = 25;

    // Calculate direction
    double dx = to.dx - from.dx;
    double dy = to.dy - from.dy;
    double distance = math.sqrt(dx * dx + dy * dy);

    if (distance < 0.01) return;

    double unitDx = dx / distance;
    double unitDy = dy / distance;

    // Adjust start and end points to be on circle edge
    Offset startPoint = Offset(
      from.dx + unitDx * radius,
      from.dy + unitDy * radius,
    );
    Offset endPoint = Offset(
      to.dx - unitDx * (radius + 5),
      to.dy - unitDy * (radius + 5),
    );

    // Draw line
    canvas.drawLine(startPoint, endPoint, linePaint);

    // Draw arrow head
    _drawArrowHead(canvas, startPoint, endPoint, arrowPaint);

    // Draw label
    Offset midPoint = Offset(
      (startPoint.dx + endPoint.dx) / 2,
      (startPoint.dy + endPoint.dy) / 2 - 10,
    );

    textPainter.text = TextSpan(
      text: label,
      style: const TextStyle(color: Colors.blue, fontSize: 12, fontWeight: FontWeight.bold),
    );
    textPainter.layout();

    // Draw white background for label
    final labelRect = Rect.fromCenter(
      center: midPoint,
      width: textPainter.width + 4,
      height: textPainter.height + 4,
    );
    canvas.drawRect(labelRect, Paint()..color = Colors.white);

    textPainter.paint(
      canvas,
      Offset(midPoint.dx - textPainter.width / 2, midPoint.dy - textPainter.height / 2),
    );
  }

  void _drawArrowHead(Canvas canvas, Offset from, Offset to, Paint paint) {
    const double arrowSize = 10;

    double dx = to.dx - from.dx;
    double dy = to.dy - from.dy;
    double angle = math.atan2(dy, dx);

    Path arrowPath = Path();
    arrowPath.moveTo(to.dx, to.dy);
    arrowPath.lineTo(
      to.dx - arrowSize * math.cos(angle - math.pi / 6),
      to.dy - arrowSize * math.sin(angle - math.pi / 6),
    );
    arrowPath.lineTo(
      to.dx - arrowSize * math.cos(angle + math.pi / 6),
      to.dy - arrowSize * math.sin(angle + math.pi / 6),
    );
    arrowPath.close();

    canvas.drawPath(arrowPath, paint);
  }

  void _drawSelfLoop(Canvas canvas, Offset pos, String label, TextPainter textPainter) {
    const double radius = 25;
    const double loopRadius = 20;

    final paint = Paint()
      ..color = Colors.black
      ..strokeWidth = 2
      ..style = PaintingStyle.stroke;

    final arrowPaint = Paint()
      ..color = Colors.black
      ..strokeWidth = 2
      ..style = PaintingStyle.fill;

    // Draw arc above the state
    Rect rect = Rect.fromCircle(
      center: Offset(pos.dx, pos.dy - radius - loopRadius),
      radius: loopRadius,
    );

    canvas.drawArc(rect, -math.pi * 0.7, math.pi * 1.4, false, paint);

    // Draw arrow head
    double arrowAngle = math.pi * 0.3;
    Offset arrowTip = Offset(
      pos.dx + loopRadius * math.cos(arrowAngle),
      pos.dy - radius - loopRadius + loopRadius * math.sin(arrowAngle),
    );

    Offset arrowFrom = Offset(
      arrowTip.dx - 10,
      arrowTip.dy,
    );

    _drawArrowHead(canvas, arrowFrom, arrowTip, arrowPaint);

    // Draw label
    textPainter.text = TextSpan(
      text: label,
      style: const TextStyle(color: Colors.blue, fontSize: 12, fontWeight: FontWeight.bold),
    );
    textPainter.layout();

    Offset labelPos = Offset(
      pos.dx - textPainter.width / 2,
      pos.dy - radius - loopRadius * 2 - 5,
    );

    // Draw white background for label
    final labelRect = Rect.fromCenter(
      center: Offset(labelPos.dx + textPainter.width / 2, labelPos.dy + textPainter.height / 2),
      width: textPainter.width + 4,
      height: textPainter.height + 4,
    );
    canvas.drawRect(labelRect, Paint()..color = Colors.white);

    textPainter.paint(canvas, labelPos);
  }

  @override
  bool shouldRepaint(covariant CustomPainter oldDelegate) => true;
}

class DFADiagramPainter extends CustomPainter {
  final DFA dfa;
  final String? currentState;

  DFADiagramPainter(this.dfa, {this.currentState});

  @override
  void paint(Canvas canvas, Size size) {
    final paint = Paint()
      ..color = Colors.black
      ..strokeWidth = 2
      ..style = PaintingStyle.stroke;

    final arrowPaint = Paint()
      ..color = Colors.black
      ..strokeWidth = 2
      ..style = PaintingStyle.fill;

    final textPainter = TextPainter(
      textDirection: TextDirection.ltr,
    );

    // Calculate positions for states in a circular layout
    Map<String, Offset> positions = {};
    List<String> stateIds = dfa.states.keys.toList()..sort();

    if (stateIds.length <= 8) {
      // Circular layout for smaller DFAs
      double centerX = size.width / 2;
      double centerY = size.height / 2;
      double radius = math.min(size.width, size.height) * 0.35;

      for (int i = 0; i < stateIds.length; i++) {
        double angle = 2 * math.pi * i / stateIds.length - math.pi / 2;
        positions[stateIds[i]] = Offset(
          centerX + radius * math.cos(angle),
          centerY + radius * math.sin(angle),
        );
      }
    } else {
      // Grid layout for larger DFAs
      int cols = math.sqrt(stateIds.length).ceil();
      int rows = (stateIds.length / cols).ceil();
      double cellWidth = size.width / (cols + 1);
      double cellHeight = size.height / (rows + 1);

      for (int i = 0; i < stateIds.length; i++) {
        int row = i ~/ cols;
        int col = i % cols;
        positions[stateIds[i]] = Offset(
          cellWidth * (col + 1),
          cellHeight * (row + 1),
        );
      }
    }

    // Draw transitions
    for (var stateId in stateIds) {
      var state = dfa.states[stateId]!;
      var fromPos = positions[stateId]!;

      Map<String, List<String>> transitionsByTarget = {};

      for (var entry in state.transitions.entries) {
        String symbol = entry.key;
        String target = entry.value;

        if (!transitionsByTarget.containsKey(target)) {
          transitionsByTarget[target] = [];
        }
        transitionsByTarget[target]!.add(symbol);
      }

      for (var entry in transitionsByTarget.entries) {
        String targetId = entry.key;
        List<String> symbols = entry.value;
        var toPos = positions[targetId]!;

        if (stateId == targetId) {
          // Self-loop
          _drawSelfLoop(canvas, fromPos, symbols.join(','), textPainter);
        } else {
          _drawArrow(canvas, fromPos, toPos, paint, arrowPaint, symbols.join(','), textPainter);
        }
      }
    }

    // Draw states
    for (var stateId in stateIds) {
      var pos = positions[stateId]!;
      bool isStart = stateId == dfa.startState;
      bool isAccept = dfa.acceptStates.contains(stateId);
      bool isCurrent = stateId == currentState;

      _drawState(canvas, pos, stateId, isStart, isAccept, textPainter, isCurrent);
    }
  }

  void _drawState(Canvas canvas, Offset pos, String label, bool isStart, bool isAccept, TextPainter textPainter, bool isCurrent) {
    final paint = Paint()
      ..color = isStart ? Colors.green : (isAccept ? Colors.blue.shade100 : Colors.white)
      ..style = PaintingStyle.fill;

    final highlightPaint = Paint()
      ..color = Colors.orange
      ..style = PaintingStyle.fill;

    final borderPaint = Paint()
      ..color = Colors.black
      ..strokeWidth = 2
      ..style = PaintingStyle.stroke;

    const double radius = 30;

    // Draw outer circle for accept states (double circle)
    if (isAccept) {
      canvas.drawCircle(pos, radius + 5, borderPaint);
    }

    // Draw main circle
    if (isCurrent) {
      canvas.drawCircle(pos, radius, highlightPaint);
    } else {
      canvas.drawCircle(pos, radius, paint);
    }
    canvas.drawCircle(pos, radius, borderPaint);

    // Draw label
    textPainter.text = TextSpan(
      text: label,
      style: const TextStyle(color: Colors.black, fontSize: 16, fontWeight: FontWeight.bold),
    );
    textPainter.layout();
    textPainter.paint(
      canvas,
      Offset(pos.dx - textPainter.width / 2, pos.dy - textPainter.height / 2),
    );

    // Draw start arrow
    if (isStart) {
      final startArrowStart = Offset(pos.dx - radius - 50, pos.dy);
      final startArrowEnd = Offset(pos.dx - radius - 5, pos.dy);
      canvas.drawLine(startArrowStart, startArrowEnd, borderPaint);
      _drawArrowHead(canvas, startArrowStart, startArrowEnd, borderPaint);
    }
  }

  void _drawArrow(Canvas canvas, Offset from, Offset to, Paint linePaint, Paint arrowPaint, String label, TextPainter textPainter) {
    const double radius = 30;

    // Calculate direction
    double dx = to.dx - from.dx;
    double dy = to.dy - from.dy;
    double distance = math.sqrt(dx * dx + dy * dy);

    if (distance < 0.01) return;

    double unitDx = dx / distance;
    double unitDy = dy / distance;

    // Adjust start and end points to be on circle edge
    Offset startPoint = Offset(
      from.dx + unitDx * (radius + 2),
      from.dy + unitDy * (radius + 2),
    );
    Offset endPoint = Offset(
      to.dx - unitDx * (radius + 7),
      to.dy - unitDy * (radius + 7),
    );

    // Draw line
    canvas.drawLine(startPoint, endPoint, linePaint);

    // Draw arrow head
    _drawArrowHead(canvas, startPoint, endPoint, arrowPaint);

    // Draw label
    Offset midPoint = Offset(
      (startPoint.dx + endPoint.dx) / 2,
      (startPoint.dy + endPoint.dy) / 2 - 12,
    );

    textPainter.text = TextSpan(
      text: label,
      style: const TextStyle(color: Colors.blue, fontSize: 14, fontWeight: FontWeight.bold),
    );
    textPainter.layout();

    // Draw white background for label
    final labelRect = Rect.fromCenter(
      center: midPoint,
      width: textPainter.width + 6,
      height: textPainter.height + 6,
    );
    canvas.drawRect(labelRect, Paint()..color = Colors.white);

    textPainter.paint(
      canvas,
      Offset(midPoint.dx - textPainter.width / 2, midPoint.dy - textPainter.height / 2),
    );
  }

  void _drawArrowHead(Canvas canvas, Offset from, Offset to, Paint paint) {
    const double arrowSize = 12;

    double dx = to.dx - from.dx;
    double dy = to.dy - from.dy;
    double angle = math.atan2(dy, dx);

    Path arrowPath = Path();
    arrowPath.moveTo(to.dx, to.dy);
    arrowPath.lineTo(
      to.dx - arrowSize * math.cos(angle - math.pi / 6),
      to.dy - arrowSize * math.sin(angle - math.pi / 6),
    );
    arrowPath.lineTo(
      to.dx - arrowSize * math.cos(angle + math.pi / 6),
      to.dy - arrowSize * math.sin(angle + math.pi / 6),
    );
    arrowPath.close();

    canvas.drawPath(arrowPath, paint);
  }

  void _drawSelfLoop(Canvas canvas, Offset pos, String label, TextPainter textPainter) {
    const double radius = 30;
    const double loopRadius = 25;

    final paint = Paint()
      ..color = Colors.black
      ..strokeWidth = 2
      ..style = PaintingStyle.stroke;

    final arrowPaint = Paint()
      ..color = Colors.black
      ..strokeWidth = 2
      ..style = PaintingStyle.fill;

    // Draw arc above the state
    Rect rect = Rect.fromCircle(
      center: Offset(pos.dx, pos.dy - radius - loopRadius),
      radius: loopRadius,
    );

    canvas.drawArc(rect, -math.pi * 0.7, math.pi * 1.4, false, paint);

    // Draw arrow head
    double arrowAngle = math.pi * 0.3;
    Offset arrowTip = Offset(
      pos.dx + loopRadius * math.cos(arrowAngle),
      pos.dy - radius - loopRadius + loopRadius * math.sin(arrowAngle),
    );

    Offset arrowFrom = Offset(
      arrowTip.dx - 10,
      arrowTip.dy,
    );

    _drawArrowHead(canvas, arrowFrom, arrowTip, arrowPaint);

    // Draw label
    textPainter.text = TextSpan(
      text: label,
      style: const TextStyle(color: Colors.blue, fontSize: 14, fontWeight: FontWeight.bold),
    );
    textPainter.layout();

    Offset labelPos = Offset(
      pos.dx - textPainter.width / 2,
      pos.dy - radius - loopRadius * 2 - 8,
    );

    // Draw white background for label
    final labelRect = Rect.fromCenter(
      center: Offset(labelPos.dx + textPainter.width / 2, labelPos.dy + textPainter.height / 2),
      width: textPainter.width + 6,
      height: textPainter.height + 6,
    );
    canvas.drawRect(labelRect, Paint()..color = Colors.white);

    textPainter.paint(canvas, labelPos);
  }

  @override
  bool shouldRepaint(covariant CustomPainter oldDelegate) => true;
}