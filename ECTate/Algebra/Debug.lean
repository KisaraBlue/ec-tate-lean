section kernel_error_message

variable {α : Type}
variable [LT α]
variable {c : α}
variable [∀ m : α, Decidable (m=c)]


theorem c_lt {a : α} (hab : a = c) : c < a := sorry

def id_of_c_lt (m : α) : c < m → α := fun _ => m

theorem minimal_error (M m: α) (hm : c < m) (m_eq_M : m = M) (M_eq_c : M = c) (H : (id_of_c_lt M (c_lt M_eq_c)) = c) : (if h : m = c then id_of_c_lt m (c_lt h) else m) = c := by
    rw [dif_pos]
    . simp only [m_eq_M]
      rw [m_eq_M] at hm --useless rewrite of an assumption makes the hc case disappear and produces cryptic kernel message
      exact H


theorem error_avoided (M m: α) (hm : c < m) (m_eq_M : m = M) (M_eq_c : M = c) (H : (id_of_c_lt M (c_lt M_eq_c)) = c) : (if h : m = c then id_of_c_lt m (c_lt h) else m) = c := by
    rw [dif_pos]
    . simp only [m_eq_M]
      exact H
    . rw [m_eq_M]
      exact M_eq_c


end kernel_error_message
