Require Import Memory Memimpl.
Require Import Unusedglobproof.

Module Mem.
Export Memimpl.Mem.
Export Unusedglobproof.Mem.

Local Existing Instances memory_model_ops memory_model_prf.
Existing Instance inject_perm_all.

Local Instance memory_model_x_prf:
  MemoryModelX mem.
Proof.
  split.
  intros.
  eapply Memimpl.Mem.zero_delta_inject; eauto.
  intros; eapply H2; eauto.
Qed.

End Mem.
