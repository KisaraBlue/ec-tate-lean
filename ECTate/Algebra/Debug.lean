section kernel_error_message

variable {α : Type}
variable [LT α]
variable [Add α]
variable {c : α}
variable [∀ m : α, Decidable (m+c=c)]
variable {c_lt_c : c < c}

theorem c_lt_sum {a b : α} (ha : c < a) (hb : c < b) (hab : a + b = c) : c < a + b := sorry

def sum_of_c_lt (m : α) : c < m → α := fun _ => m + c

theorem minimal_error (M m: α) (hm : c < m) (hM : c < M) (m_eq_M : m = M) (add_M_c : M + c = c) (H : (sum_of_c_lt (M + c) (c_lt_sum hM (c_lt_c) add_M_c)) = c) : (if hmq : m + c = c then sum_of_c_lt (m + c) (c_lt_sum hm (c_lt_c) hmq) else m) = c := by
    rw [dif_pos]
    . simp only [m_eq_M]
      rw [m_eq_M] at hm --useless rewrite of an assumption makes the hc case disappear and produces cryptic kernel message
      exact H


theorem error_avoided (M m: α) (hm : c < m) (hM : c < M) (m_eq_M : m = M) (add_M_c : M + c = c) (H : (sum_of_c_lt (M + c) (c_lt_sum hM (c_lt_c) add_M_c)) = c) : (if hmq : m + c = c then sum_of_c_lt (m + c) (c_lt_sum hm (c_lt_c) hmq) else m) = c := by
    rw [dif_pos]
    . simp only [m_eq_M]
      exact H
    . rw [m_eq_M]
      exact add_M_c


end kernel_error_message
