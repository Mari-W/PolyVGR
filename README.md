# Polymorphic Imperative Session Types

```
∀(𝑛 ′ : Shape).∀( Σ̂ ′ : Dom(𝑛 ′) → State).
∀(𝑛 ′′ : Shape).∀( Σ̂ ′′ : Dom(𝑛 ′′) → State).∀(𝑇ˆ ′′ : Dom(𝑛 ′′) → Type).
∀(𝛼 ′ : Dom(𝑛 ′)).∀(𝛼 ′′ : Dom(𝑛 ′′)).∀(𝛾 : Dom(X)). (𝛼 ′ # 𝛾, 𝛼 ′′ # 𝛾) ⇒
∀(𝜎 : Session).∀(𝜎 ′ : Session).
( · ; ( Σ̂ ′ 𝛼 ′, 𝛾 ↦→ 𝜎; Chan 𝛾 → Σ̂ ′′ 𝛼 ′′, 𝛾 ↦→ 𝜎 ′; 𝑇ˆ ′′ 𝛼 ′′) →
· ; ( Σ̂ ′ 𝛼 ′, 𝛾 ↦→ !(∃𝛼 : Dom(I). · ; Int).𝜎; Chan 𝛾 → Σ̂ ′′ 𝛼 ′′, 𝛾 ↦→ 𝜎 ′; 𝑇ˆ ′′ 𝛼 ′′))
```