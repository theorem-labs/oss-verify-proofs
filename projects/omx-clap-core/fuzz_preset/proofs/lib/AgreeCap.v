From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import AllocSlots AllocRoom AgreeLim AgreeRoom.
Local Open Scope Z_scope.

Definition CAP_AG : Z := 1024.

Lemma CAP_AG_ge : 512 <= CAP_AG.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma CAP_AG_le_CAPMAX : CAP_AG <= CAPMAX.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma CAP_AG_fits : LIVE_BOUND CAP_AG (2 ^ 29) + NONHEAP_CF <= 2 ^ 34.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma CAP_AG_fits39 : LIVE_BOUND CAP_AG (2 ^ 36) + NONHEAP_CF <= LIM_AG.
Proof. rewrite LIM_AG_eq. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma room_cf_of_limit : forall md b n, 2 ^ 34 <= vm_limit (m_vmmaps md) -> room_slots b n ->
  0 <= sb_cap b <= CAP_AG -> sb_bytes b + n <= 2 ^ 29 -> room_cf md b n.
Proof.
  intros md b n Hl. apply (room_cf_of_bound CAP_AG (2 ^ 29)). pose proof CAP_AG_fits. lia.
Qed.

Lemma room_cf_of_limit39 : forall md b n, LIM_AG <= vm_limit (m_vmmaps md) -> room_slots b n ->
  0 <= sb_cap b <= CAP_AG -> sb_bytes b + n <= 2 ^ 36 -> room_cf md b n.
Proof.
  intros md b n Hl. apply (room_cf_of_bound CAP_AG (2 ^ 36)). pose proof CAP_AG_fits39. lia.
Qed.
