(* The slot count the placement policy's search window holds.  PolicyFit.win_room_of_slots turns
   [nslots + KRES <= slot_capW R] into the window count for a request of R bytes, with the ledger's bytes bounded by
   the run's budget (vm_limit <= LIM_AG = 2^39) plus the image's reserved bytes (2^30).
   WCAPN = PolicyFit.WNUM - 2^39 - 2^30 - 24 * PGSZ - MG_REQ. *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05 YO0i PlaceCap YO0d.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Definition WCAPN : Z := 104815536619520.

Definition slot_capW (R : Z) : Z := WCAPN / (page_round R + PGSZ) - 2.

Lemma slot_capW_anti : forall R1 R2, 0 < R1 <= R2 -> slot_capW R2 <= slot_capW R1.
Proof.
intros R1 R2 H. unfold slot_capW.
pose proof (slot_round_ge R1). pose proof (slot_round_mono R1 R2 ltac:(lia)).
assert (D : WCAPN / (page_round R2 + PGSZ) <= WCAPN / (page_round R1 + PGSZ)).
{ apply Z.div_le_compat_l; [unfold WCAPN; lia | unfold PGSZ; lia]. }
lia.
Qed.

Lemma slot_capW_ge : forall R, 0 < R <= MG_REQ -> MG_SLOTS + KRES <= slot_capW R.
Proof.
intros R HR. pose proof (slot_capW_anti R MG_REQ HR) as A.
assert (C : MG_SLOTS + KRES <= slot_capW MG_REQ) by (apply Z.leb_le; vm_compute; reflexivity).
lia.
Qed.

Lemma slot_capW_mul : forall R K, 0 <= R -> K <= slot_capW R -> (K + 2) * (page_round R + PGSZ) <= WCAPN.
Proof.
intros R K HR HK. unfold slot_capW in HK.
pose proof (slot_round_ge R). set (d := page_round R + PGSZ) in *.
assert (Hd : 0 < d) by (unfold d, PGSZ; lia).
pose proof (Z.mul_div_le WCAPN d Hd).
assert (K + 2 <= WCAPN / d) by lia.
pose proof (Z.mul_le_mono_nonneg_r (K + 2) (WCAPN / d) d ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma page_round_idem : forall R, page_round (page_round R) = page_round R.
Proof.
intros R. unfold page_round, PGSZ.
set (k := (R + 4096 - 1) / 4096).
replace (k * 4096 + 4096 - 1) with (k * 4096 + 4095) by lia.
rewrite Z.div_add_l by lia. replace (4095 / 4096) with 0 by reflexivity. lia.
Qed.
