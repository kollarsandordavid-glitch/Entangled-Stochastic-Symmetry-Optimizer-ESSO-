Part of Jaide LLM



Entangled Stochastic Symmetry Optimizer (ESSO)
Ez a fájl egy Entangled Stochastic Symmetry Optimizer (ESSO) implementációja Zig programozási nyelven. A neve – esso_optimizer.zig – pontosan leírja a funkcióját: egy összegabalyodott (entanglement-alapú), sztochasztikus, szimmetria-vezérelt optimalizációs rendszer, amelyet egy önhasonló relációs gráfon (SelfSimilarRelationalGraph) hajt végre szimulált lehűlés (simulated annealing) segítségével.

Fő architekturális komponensek
SymmetryGroup és SymmetryTransform
A fájl alapvető absztrakciója a szimmetriacsoport enum, amely hat transzformációt definiál: identity, reflection, rotation_90, rotation_180, rotation_270, és translation. A SymmetryTransform struktúra ezeket a transzformációkat tárolja origóval, paraméterekkel és skálafaktorral, és képes alkalmazni őket 2D pontokra (apply), komplex számokra (applyToComplex), és kvantumállapotokra (applyToQuantumState). A compose metódus két transzformáció mátrixszorzatát számolja ki és visszavezeti egy ismert csoportelemre – ez a csoportelméleti koherenciát biztosítja.

EntanglementInfo – Összefonódás-kezelés
Az EntanglementInfo struktúra egy csomópár kvantum-összegabalyodásának állapotát kezeli, tárolva a korrelációs erősséget (correlation_strength), fáziskülönbséget (phase_difference), interakciószámot és időbélyegeket. A getDecayFactor metódus exponenciális bomlást számol a megadott felezési idő (half_life_ms) alapján az alábbi képlet szerint: D(t) = e^{-\ln(2) \cdot (t / t_{1/2})}, ahol t az eltelt idő milliszekundumban, t_{1/2} pedig a felezési idő. Az update metódus mozgóátlag-módszerrel frissíti a korrelációt, és cirkuláris átlagolással számolja a fázist, elkerülve a 0° és 360° körüli ugrásokat.

OptimizationState – Állapotreprezentáció
Az OptimizationState fogja össze az aktuális gráfot, az energiaértéket, az entanglement százalékos arányát és az összes összefonódott csomópárt egy egyedi HashMap-ben. A kulcshoz egy egyéni NodePairKeyContext hash-kontextust használ, amely Wyhash-alapon hash-eli a csomópárok stringjét. Az addEntanglement metódus lexikográfiai sorrendbe rendezi a párokat (n1 < n2), így bármely irányból lekérdezhető az összefonódás. A clone metódus mély másolatot készít mind a gráfról, mind az entanglement-térképről – ez kritikus a legjobb állapot biztonságos megőrzéséhez.

OptimizationStatistics – Statisztika
A statisztika-struktúra 16 mezőt tartalmaz, köztük az elfogadási arányt (acceptance_rate), az iterációsebességet (iterationsPerSecond), a hőmérséklettörténetet, a felfedezett szimmetriák számát és a lokális minimumoktól való menekülések számát. A isConverged metódus akkor jelzi a konvergenciát, ha legalább 10 iteráció után az energiaváltozás egy megadott küszöb alá esik, és legalább egy lépés elfogadásra került.

Az EntangledStochasticSymmetryOptimizer főstruktúra
Ez a fájl legösszetettebb és legfontosabb struktúrája. Szimulált lehűlésen (Simulated Annealing) alapuló optimalizátort valósít meg, amely hét különböző lépéstípust (applyMove) alkalmaz véletlenszerűen.

A hét lépéstípus (applyMove)
Az applyMove függvény egy 0–6 közötti egész alapján választ lépéstípust.

Élsúly-perturbáció: Minden él súlyát véletlenszerűen megváltoztatja a hőmérséklettel arányos mértékben, [0, 1] intervallumra szorítva az értéket.
Csomópont-fázis perturbáció: Minden csomópont kvantumfázisát megzavarja, a változás a hőmérséklettel arányos, és [0, 2π] körüli marad.
Új összefonódás létrehozása: createNewEntanglementInPlace – véletlenszerűen választ két csomópontot, és ha még nem összegabalyodtak, létrehoz egy új EntanglementInfo bejegyzést 0.5–1.0 közötti korrelációval.
Szimmetria-transzformáció alkalmazása: Ha van detektált szimmetria, véletlenszerűen választ egyet, és az összes csomópont kvantumállapotát és fázisát a szimmetriával transzformálja.
Qubit-vektor perturbáció: Minden csomópont qubitjének a és b amplitúdóját megzavarja véletlenszerű szög irányban, majd renormálja az állapotot |a|^2 + |b|^2 = 1 feltételre.
Fraktáldimenziós perturbáció: Minden él fractal_dimension értékét módosítja kis mértékben, [0, 3] intervallumra szorítva.
Véletlenszerű él ki/bekapcsolás: toggleRandomEdge – egy teljesen klónozott gráfon dolgozik, és véletlenszerűen töröl vagy felvesz egy élt két csomópont között.
Az UndoLog mechanizmus
A UndoLog struktúra lehetővé teszi az elfogadhatatlan lépések visszavonását anélkül, hogy minden iterációban teljes gráf-klónozás kellene. Az él- és csomóponti értékeket listában tárolja, a 6-os típusnál (toggled edge) viszont az egész régi gráf-pointert tárolja el, és visszalépéskor egyszerűen cseréli a pointert. Ez hatékony: 0–5-ös lépéseknél csak a megváltozott értékek kerülnek mentésre.

Adaptív hűtés (adaptiveCoolTemperature)
Ha az elfogadási arány 60% fölé megy, a rendszer gyorsabb hűtéssel reagál (szorzó: 0.98), ha 20% alá esik, lassít (szorzó: 1.02). Ez biztosítja, hogy az optimalizátor ne hűljön le túl gyorsan jó megoldások esetén, de ne is ragadjon bele lokális minimumokba. Ezen felül, ha a stagnálás meghaladja az iterációk 10%-át, a hőmérséklet a reheat_factor-ral (alapértelmezetten 2.0) megszorzódik – ez a lokális minimumokból való menekülés mechanizmusa.

Szimmetriadetekció (detectSymmetries)
A szimmetriadetekció heurisztikus algoritmus, amely a gráf csomópontjainak fokszám-eloszlása és kvantumfázisai alapján azonosít szimmetriákat. Mindig hozzáadja az identity transzformációt. Tükrözési szimmetriát akkor javasol, ha a fokszám-eloszlásban legfeljebb egy páratlan multiplicitású fokszám van. A 90°-os rotáció csak akkor detektált, ha minden fokszám multiplicitása 4 többszöröse, és legalább 4 csomópont van. A 180°-os rotációs szimmetriát fázisalapú heurisztika jelzi: ha a csomópontok legalább felének fázisa közel van az átlagfázishoz (±0.1 tolerancián belül).

Célértékfüggvények
A fájl négy különböző objektívfüggvényt definiál, amelyek cserélhetők:

defaultGraphObjective: Összeadja az összes él weight × fractal_dimension értékét, a kvantumkorrelációs amplitúdókat, a csomópontok fáziskoszinuszát, a qubit-amplitúdókat, és hozzáadja az átlagos összefonódást. Ez egy általános, vegyes energiafüggvény.
connectivityObjective: Minimalizálja az összefüggőség hiányát és az alacsony átlagsúlyokat – (1 − connectivity_ratio) + (1 − avg_weight) formában.
quantumCoherenceObjective: A kvantumkoherencia (qubit-amplitúdók és fázisok) és az élkorrelációk alapján számol értéket, [0, 1] intervallumra normálva.
fractalDimensionObjective: Az átlagos fractal_dimension eltérését minimalizálja egy 1.5-ös célértéktől.
Memóriakezelés és biztonság
A Zig sajátosságaként az összes heap-allokált erőforrás explicit deinit hívással szabadul fel. Az errdefer konstrukciók gondoskodnak arról, hogy hiba esetén se legyen memóriaszivárgás – különösen a clone, optimize, és toggleRandomEdge függvényekben. Az owns_graph flag szabályozza, hogy az OptimizationState felelős-e a gráf felszabadításáért: a klónolt állapotoknál true, az externálisan átadott gráfoknál false. A tesztek (test blokkok) std.testing.allocator-t használnak, amely szivárgást detektál, így a kód memória-helyessége automatikusan ellenőrzött.
