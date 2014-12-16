module Testing where
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + m = m
  (succ n) + m = n + (succ m)
  
  data _even : ℕ → Set where
    ZERO : zero even
    STEP : ∀ (x : ℕ) → x even → (succ (succ x)) even

  proof₁ : (succ (succ (succ (succ zero)))) even
  proof₁ = STEP (succ (succ zero)) (STEP zero ZERO)

  data _eq_ : ℕ → ℕ → Set where
    REFLEQ : ∀ (x : ℕ) → x eq x
    SYMMEQ : ∀ (x : ℕ) → ∀ (y : ℕ) → (x eq y) → (y eq x)
    TRNSEQ : ∀ (x : ℕ) → ∀ (y : ℕ) → ∀ (z : ℕ) → (x eq y) → (y eq z) → (x eq z)

  -- 1 = 1, my greatest contribution to mathematics
  proof₂ : (succ zero) eq (succ zero)
  proof₂ = REFLEQ (succ zero)

  proof₃ : ∀ (n : ℕ) → ((zero + n) eq n)
  proof₃ = REFLEQ

  proof₄ : ∀ (n : ℕ) → ((n + zero) eq (zero + n))
  proof₄ = λ n → {!!}
