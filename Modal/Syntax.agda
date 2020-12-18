data Form : Set where
  ⊤ : Form
  ⊥ : Form
  ¬ : Form -> Form
  □ : Form -> Form
  ◇ : Form -> Form
  ∧ : Form -> Form -> Form
  ∨ : Form -> Form -> Form
  ⟶ : Form -> Form -> Form

form-size : Form → ℕ 
  from-size ⊤ : 0
  from-size ⊥ : 0
  from-size f : 1
  from-size ¬ f : 1 + from-size f + from-size f'
  from-size □ f : 1 + from-size f + from-size f'
  from-size ◇ f : 1 + from-size f + from-size f'
  from-size f ∧ f' : 1 + from-size f + from-size f'
  from-size f ∨ f' : 1 + from-size f + from-size f'
  from-size f ⟶ f' : 1 + from-size f + from-size f'


