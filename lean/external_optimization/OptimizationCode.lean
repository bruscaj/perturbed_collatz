import OptimizationAlgorithmTypes

/-! A total, deliberately exhaustive natural-number program. No real tests,
classical minimizers or canonical optimalNumerator occur in this executable code.
Correctness against the original graph is a separate proof obligation. -/
namespace ExternalO3OptimizationCode

abbrev Input := ℕ × ℕ × ℕ

def depth (p : Input) : ℕ := p.1 + 1
def base (p : Input) : ℕ := p.2.1 + 2
def cap (p : Input) : ℕ := p.2.2 + 2
def vertices (p : Input) : ℕ := base p ^ depth p
def edges (p : Input) : ℕ := cap p * vertices p

def foldTo {α : Type} (n : ℕ) (z : α) (f : ℕ → α → α) : α :=
  n.rec z (fun i v => f i v)

def sumTo (n : ℕ) (f : ℕ → ℕ) : ℕ := foldTo n 0 (fun i v => v + f i)
def allTo (n : ℕ) (f : ℕ → Bool) : Bool := foldTo n true (fun i v => v && f i)

def digit (M v i : ℕ) : ℕ := v / M ^ i % M
def digitSum (M h v : ℕ) : ℕ := sumTo h (digit M v)

/-- Every tag has N slots. Tag 0 is ascending; tags 1,...,J-1 are K=tag+1 exits. -/
def tag (p : Input) (e : ℕ) : ℕ := e / vertices p
def vertex (p : Input) (e : ℕ) : ℕ := e % vertices p

def valid (p : Input) (e : ℕ) : Bool :=
  decide (e < edges p) && (decide (tag p e ≠ 0) || decide (0 < vertex p e % base p))

def source (p : Input) (e : ℕ) : ℕ :=
  if tag p e = 0 then vertex p e
  else base p * (vertex p e % base p ^ (depth p - 1))

def target (p : Input) (e : ℕ) : ℕ :=
  if tag p e = 0 then vertex p e - 1 else vertex p e

def halvings (p : Input) (e : ℕ) : ℕ := if tag p e = 0 then 1 else tag p e + 1

def exponent (p : Input) (e : ℕ) : ℕ :=
  (if tag p e = 0 then 0 else halvings p e) + depth p +
    digitSum (base p) (depth p) (vertex p e)

def common (p : Input) : ℕ := cap p + depth p * base p
def units (p : Input) (e : ℕ) : ℕ := 2 ^ (common p - exponent p e)

def deleted (mask e : ℕ) : Bool := decide (mask / 2 ^ e % 2 = 1)
def edgeAt (p : Input) (q i : ℕ) : ℕ := digit (edges p) q i

def wordHalvings (p : Input) (n q : ℕ) : ℕ := sumTo n (fun i => halvings p (edgeAt p q i))

/-- Only nondeleted valid edges enter a closed word; loops and parallel labels remain distinct. -/
def survivingClosed (p : Input) (mask n q : ℕ) : Bool := allTo n (fun i =>
  valid p (edgeAt p q i) && !deleted mask (edgeAt p q i) &&
  decide (target p (edgeAt p q i) = source p (edgeAt p q ((i + 1) % n))))

/-- All lengths 1,...,N, and all E^length words, including repeated-edge words. -/
def safe (p : Input) (mask : ℕ) : Bool := allTo (vertices p) (fun k =>
  allTo (edges p ^ (k + 1)) (fun q =>
    !survivingClosed p mask (k + 1) q || decide (3 ^ (k + 1) < 2 ^ wordHalvings p (k + 1) q)))

def cost (p : Input) (mask : ℕ) : ℕ := sumTo (edges p) (fun e =>
  if valid p e && deleted mask e then units p e else 0)

def allCost (p : Input) : ℕ := sumTo (edges p) (fun e => if valid p e then units p e else 0)

/-- Total bounded search, initialized with deleting all valid edges. This is a
program candidate; its canonical numerator equality is NOT built into the definition. -/
def optimizer (p : Input) : ℕ := foldTo (2 ^ edges p) (allCost p) (fun mask best =>
  if safe p mask then min best (cost p mask) else best)

end ExternalO3OptimizationCode
