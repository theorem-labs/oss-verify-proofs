(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l X09j X071.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X106.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition A_LLVMFuzzerTestOneInput : Z := 0x96754.
Definition RA_h_smalloc : Z := 0x967cc.
Definition HF_SIZE : Z := 9280.
Definition HF_DESC : Z := 0x22832.
Definition H_TRAP : Z := 0x97670.

Definition A_CH : Z := 0x96d04.
Definition A_PB : Z := 0x96d6c.
Definition A_PN : Z := 0x96ee8.
Definition A_PX : Z := 0x97418.
Definition A_KH : Z := 0x96f10.
Definition A_DH : Z := 0x96fd0.
Definition A_CL : Z := 0x974a8.
Definition A_XT : Z := 0x974b0.
Definition A_EP : Z := 0x974bc.

Definition HO_ENH : Z := 32.
Definition HO_CBK : Z := 48.
Definition HO_OUT : Z := 128.
Definition HO_FSZ : Z := 8384.
Definition HO_BITS : Z := 8400.
Definition HO_OY : Z := 8480.
Definition HO_OG : Z := 8544.
Definition HO_OP : Z := 8608.
Definition HO_OS : Z := 8688.
Definition HO_STEREO : Z := 9168.
Definition HO_RATE : Z := 9232.
Definition HO_LOOK : Z := 9248.

Definition SL_SF16 : Z := 0.               Definition SL_F8 : Z := 8.
Definition SL_F16 : Z := 16.        Definition SL_DATA : Z := 24.
Definition SL_CBKD : Z := 32.              Definition SL_BREM : Z := 40.
Definition SL_SKIP : Z := 48.           Definition SL_PNP : Z := 56.
Definition SL_RATE : Z := 64.                                Definition SL_CBK : Z := 72.
Definition SL_GFS : Z := 80.                   Definition SL_SIZE : Z := 88.
Definition SL_ENH : Z := 96.                          Definition SL_EXTRA : Z := 104.
Definition SL_OY : Z := 112.                                   Definition SL_SHB : Z := 120.
Definition SL_STEREO : Z := 128.                           Definition SL_LASTG : Z := 136.
Definition SL_OG : Z := 144.                                   Definition SL_OS : Z := 152.
Definition SL_OP : Z := 160.                                   Definition SL_SSER : Z := 168.
Definition SL_LOOK : Z := 176.                          Definition SL_FSZ : Z := 184.
Definition SL_BITS : Z := 192.                               Definition SL_NFR : Z := 200.
Definition SL_OUT : Z := 208.                               Definition SL_ST : Z := 216.
Definition SL_FAKE : Z := 240.

Definition hsp (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 : word) : list cell :=
[C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216; C8 w224; C8 w232; C8 w240].
Lemma hsp_size : forall w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240,
cells_size (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) = 248%nat.
Proof. reflexivity. Qed.

Lemma lor_byte_shift_h : forall a R, 0 <= a < 256 -> 0 <= R -> Z.lor a (Z.shiftl R 8) = a + 256 * R.
Proof.
intros a R Ha HR.
assert (L0 : Z.land a (Z.shiftl R 8) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases n 8) as [L|G]; [rewrite Z.shiftl_spec_low by lia; apply andb_false_r|].
destruct (Z.eq_dec a 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
rewrite (Z.bits_above_log2 a n); [reflexivity| lia|]. apply Z.lt_le_trans with 8; [|exact G]. apply Z.log2_lt_pow2; [lia|]. change (2^8) with 256. lia. }
rewrite <- Z.lxor_lor by exact L0. rewrite <- Z.add_nocarry_lxor by exact L0. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. lia.
Qed.
Lemma bytes_le_to_Z_bound_h : forall bs, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
induction bs as [|b bs IH]; [cbn; lia|].
cbn [bytes_le_to_Z length]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
replace (8 * Z.of_nat (S (length bs))) with (8 * Z.of_nat (length bs) + 8) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256. rewrite lor_byte_shift_h by lia. nia.
Qed.
Lemma Z_to_le_bytes_of_bytes_h : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [bytes_le_to_Z length Z_to_le_bytes]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
pose proof (bytes_le_to_Z_bound_h bs) as B. rewrite lor_byte_shift_h by lia. f_equal.
- apply zb8_eq. replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs); [exact IH|].
apply Z.div_unique with (r := bv_unsigned b); [left; lia| lia].
Qed.
Lemma le8_of_bytes_h : forall j : list byte, length j = 8%nat -> le8 (le_bytes_to_word j) = j.
Proof.
intros j L. unfold le8, word_to_le_bytes, le_bytes_to_word.
pose proof (bytes_le_to_Z_bound_h j) as B. rewrite L in B. change (8 * Z.of_nat 8) with 64 in B.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small by lia.
rewrite <- L at 1. apply Z_to_le_bytes_of_bytes_h.
Qed.
Lemma CB_C8s_h : forall n (j : list byte), length j = (8 * n)%nat -> exists ws : list word, length ws = n /\ cells_bytes (map C8 ws) = j.
Proof.
induction n as [|n IH]; intros j L.
- exists []. split; [reflexivity|]. destruct j; [reflexivity| cbn in L; lia].
- destruct (IH (skipn 8 j)) as (ws & Lws & E); [rewrite length_skipn; lia|].
exists (le_bytes_to_word (firstn 8 j) :: ws). split; [cbn; lia|].
cbn [map cells_bytes cbytes]. rewrite E, le8_of_bytes_h by (rewrite length_firstn; lia). apply firstn_skipn.
Qed.
Lemma cells_wf_C8s_h : forall ws : list word, cells_wf (map C8 ws).
Proof. induction ws; cbn; auto. Qed.

Lemma hsp_of_CB : forall (m : word -> option byte) A js, rw_cells bsegs m A [CB 248 js] ->
exists w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240,
rw_cells bsegs m A (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240).
Proof.
intros m A js H.
assert (L : length js = (8 * 31)%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
destruct (CB_C8s_h 31 js L) as (ws & Lws & E).
destruct ws as [|w0 [|w8 [|w16 [|w24 [|w32 [|w40 [|w48 [|w56 [|w64 [|w72 [|w80 [|w88 [|w96 [|w104 [|w112 [|w120 [|w128 [|w136 [|w144 [|w152 [|w160 [|w168 [|w176 [|w184 [|w192 [|w200 [|w208 [|w216 [|w224 [|w232 [|w240 [|? ?]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; try discriminate Lws.
exists w0, w8, w16, w24, w32, w40, w48, w56, w64, w72, w80, w88, w96, w104, w112, w120, w128, w136, w144, w152, w160, w168, w176, w184, w192, w200, w208, w216, w224, w232, w240.
eapply rw_cells_recast; [exact H| apply (cells_wf_C8s_h [w0; w8; w16; w24; w32; w40; w48; w56; w64; w72; w80; w88; w96; w104; w112; w120; w128; w136; w144; w152; w160; w168; w176; w184; w192; w200; w208; w216; w224; w232; w240])|]. cbn [cells_bytes cbytes app] in *. rewrite app_nil_r. exact E.
Qed.

Definition HSH_P1 : list byte := map (Z_to_bv 8) [-15; -15; -15; -15; -8; -14; -8; -8; -8; -8; -8; -14; -14; -14; -14; -14].
Definition HSH_L_HDR : list byte := map (Z_to_bv 8) [-15; -15; -15; -15; 4; -14; 0; 0; 0; 0; 0; -14; -14; -14; -14; -14].
Definition HSH_P2 : list byte := map (Z_to_bv 8) (zruns [(-14, 32%nat); (-8, 1%nat); (-14, 1%nat); (-8, 6%nat); (-14, 4%nat); (-8, 4%nat); (-14, 4%nat); (-8, 4%nat);
(-14, 4%nat); (-8, 6%nat); (-14, 4%nat); (-8, 51%nat); (-14, 9%nat); (-8, 3%nat); (-14, 5%nat); (-8, 1%nat); (-14, 1%nat); (-8, 1%nat); (-13, 3%nat)]).
Definition HSH_P3 : list byte := map (Z_to_bv 8) (zruns [(-14, 32%nat); (4, 1%nat); (-14, 1%nat); (0, 6%nat); (-14, 4%nat); (0, 4%nat); (-14, 4%nat); (0, 4%nat);
(-14, 4%nat); (0, 6%nat); (-14, 4%nat); (0, 51%nat); (-14, 9%nat); (0, 3%nat); (-14, 5%nat); (-8, 1%nat); (-14, 1%nat); (-8, 1%nat); (-13, 3%nat)]).
Definition HSH_T : list byte := map (Z_to_bv 8) (zruns [(-14, 32%nat); (4, 1%nat); (-14, 1%nat); (0, 6%nat); (-14, 4%nat); (0, 4%nat); (-14, 4%nat); (0, 4%nat);
(-14, 4%nat); (0, 6%nat); (-14, 4%nat); (0, 51%nat); (-14, 9%nat); (0, 3%nat); (-14, 5%nat); (4, 1%nat); (-14, 1%nat); (4, 1%nat); (-13, 3%nat)]).

Definition HSH_R : list byte := repeat (Z_to_bv 8 0) 1000 ++ HSH_T.
Definition HSH_MAIN : list byte := HSH_P1 ++ HSH_R.
Definition HSH_HDR : list byte := HSH_L_HDR ++ HSH_R.
Lemma HSH_MAIN_length : length HSH_MAIN = 1160%nat.  Proof. reflexivity. Qed.
Lemma HSH_HDR_length : length HSH_HDR = 1160%nat.  Proof. reflexivity. Qed.
Lemma HSH_R_length : length HSH_R = 1144%nat.  Proof. reflexivity. Qed.

Lemma hsh_slice_acc : forall (m : word -> option byte) (F : Z) (sh : list byte) (o n : Z),
F mod 8 = 0 -> 0 <= F -> o mod 8 = 0 -> 0 <= o -> 0 <= n ->
bytes_at bsegs m (shad F) sh -> (Z.to_nat (o / 8) + length (ushadow n) <= length sh)%nat ->
firstn (length (ushadow n)) (skipn (Z.to_nat (o / 8)) sh) = ushadow n ->
acc bsegs m (F + o) n.
Proof.
intros m F sh o n F8 F0 O8 O0 N0 B L E.
apply acc_ushadow; [rewrite Zplus_mod, F8, O8; reflexivity| lia| lia|].
rewrite (shad_aligned_add F o F8 O0).
pose proof (bytes_at_sub m (shad F) sh (Z.to_nat (o / 8)) (length (ushadow n)) B ltac:(lia)) as X.
rewrite E, Z2Nat.id in X by (apply Z.div_pos; lia). exact X.
Qed.

Lemma hsh_R_acc : forall (m : word -> option byte) (F : Z),
F mod 8 = 0 -> 0 <= F -> bytes_at bsegs m (shad F + 16) HSH_R ->
acc bsegs m (F + HO_OUT) 8000 /\ acc bsegs m (F + HO_FSZ) 4 /\ acc bsegs m (F + HO_BITS) BITS_SIZEOF /\ acc bsegs m (F + HO_OY) 32
/\ acc bsegs m (F + HO_OG) 32 /\ acc bsegs m (F + HO_OP) 48 /\ acc bsegs m (F + HO_OS) 408 /\ acc bsegs m (F + HO_STEREO) 24
/\ acc bsegs m (F + HO_RATE) 4 /\ acc bsegs m (F + HO_LOOK) 4.
Proof.
intros m F F8 F0 B.
assert (B' : bytes_at bsegs m (shad F) (repeat (Z_to_bv 8 0) 16 ++ HSH_R) -> True) by (intros; exact I).
clear B'.

assert (SL : forall o n, o mod 8 = 0 -> 128 <= o -> 0 <= n -> (Z.to_nat (o / 8 - 16) + length (ushadow n) <= length HSH_R)%nat ->
firstn (length (ushadow n)) (skipn (Z.to_nat (o / 8 - 16)) HSH_R) = ushadow n -> acc bsegs m (F + o) n).
{ intros o n O8 O128 N0 L E.
apply acc_ushadow; [rewrite Zplus_mod, F8, O8; reflexivity| lia| lia|].
rewrite (shad_aligned_add F o F8 ltac:(lia)).
pose proof (bytes_at_sub m (shad F + 16) HSH_R (Z.to_nat (o / 8 - 16)) (length (ushadow n)) B L) as X.
rewrite E, Z2Nat.id in X by (apply Z.le_0_sub; apply Z.div_le_lower_bound; lia).
replace (shad F + o / 8) with (shad F + 16 + (o / 8 - 16)) by lia. exact X. }
unfold HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK, BITS_SIZEOF.
repeat split; (apply SL; [reflexivity| lia| lia| vm_compute; lia| vm_compute; reflexivity]).
Qed.

Lemma hsh_L_hdr_acc : forall (m : word -> option byte) (F : Z),
F mod 8 = 0 -> 0 <= F -> bytes_at bsegs m (shad F) HSH_L_HDR ->
acc bsegs m (F + HO_ENH) 4 /\ acc bsegs m (F + HO_CBK) 40.
Proof.
intros m F F8 F0 B. unfold HO_ENH, HO_CBK.
split; (apply (hsh_slice_acc m F HSH_L_HDR); [exact F8| exact F0| reflexivity| lia| lia| exact B| vm_compute; lia| vm_compute; reflexivity]).
Qed.

Lemma rw_CB_cut : forall segs (m : word -> option byte) A (n k : nat) js, (k <= n)%nat -> rw_cells segs m A [CB n js] ->
exists j1 j2, rw_cells segs m A [CB k j1] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k) j2].
Proof.
intros segs m A n k js K H. apply (rw_cells_split_CB segs m A [] n js [] [k; n - k]%nat) in H; [| cbn; lia].
cbn [mk_CB_cells app] in H. apply (proj1 (rw_cells_app segs m A [CB k _] [CB (n - k) _])) in H. destruct H as (H1 & H2). cbn [cells_size csize] in H2.
do 2 eexists. split; [exact H1|]. rewrite Nat.add_0_r in H2. exact H2.
Qed.
Ltac cb_cut H k H1 :=
lazymatch type of H with rw_cells ?segs ?m ?A [CB ?n ?js] =>
let r := eval vm_compute in (n - k)%nat in
let zk := eval vm_compute in (Z.of_nat k) in
let j1 := fresh "j" in let j2 := fresh "j" in let H2 := fresh "H" in
destruct (rw_CB_cut segs m A n k js ltac:(apply Nat.leb_le; vm_compute; reflexivity) H) as (j1 & j2 & H1 & H2);
clear H; change (n - k)%nat with r in H2; change (Z.of_nat k) with zk in H2;
lazymatch A with
| (?B + ?c)%Z => let c' := eval vm_compute in (c + zk)%Z in replace (A + zk)%Z with (B + c')%Z in H2 by lia
| _ => idtac
end;
rename H2 into H
end.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition A_LLVMFuzzerTestOneInput : Z := 0x96668.
Definition RA_h_smalloc : Z := 0x966e0.
Definition HF_SIZE : Z := 9280.

Definition A_CH : Z := 0x96c04.
Definition A_PB : Z := 0x96c68.
Definition A_PN : Z := 0x9714c.
Definition A_PX : Z := 0x97174.
Definition A_KH : Z := 0x96d60.
Definition A_DH : Z := 0x96dec.
Definition A_CL : Z := 0x971a4.
Definition A_XT : Z := 0x971fc.

Definition HO_ENH : Z := 32.
Definition HO_CBK : Z := 48.
Definition HO_OUT : Z := 128.
Definition HO_FSZ : Z := 8384.
Definition HO_BITS : Z := 8400.
Definition HO_OY : Z := 8480.
Definition HO_OG : Z := 8544.
Definition HO_OP : Z := 8608.
Definition HO_OS : Z := 8688.
Definition HO_STEREO : Z := 9168.
Definition HO_RATE : Z := 9232.
Definition HO_LOOK : Z := 9248.

Definition SL_CBK : Z := 16.  Definition SL_F : Z := 32.   Definition SL_FREE4 : Z := 40.  Definition SL_LOOK : Z := 48.  Definition SL_RATE : Z := 56.
Definition SL_ENH : Z := 64.  Definition SL_DATA : Z := 72. Definition SL_NBREAD : Z := 80. Definition SL_BREM : Z := 88. Definition SL_SHB : Z := 96.
Definition SL_GFS : Z := 104. Definition SL_EXTRA : Z := 112. Definition SL_OY : Z := 120. Definition SL_EOS : Z := 128. Definition SL_NFR : Z := 136.
Definition SL_LASTG : Z := 144. Definition SL_OS : Z := 152. Definition SL_STEREO : Z := 160. Definition SL_FSZ : Z := 168. Definition SL_SSER : Z := 176.
Definition SL_CHAN : Z := 184. Definition SL_FAKE : Z := 208.

Definition hsp (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 : word) : list cell :=
[C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128;
C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208].
Lemma hsp_size : forall w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208,
cells_size (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) = 216%nat.
Proof. reflexivity. Qed.

Lemma lor_byte_shift_h : forall a R, 0 <= a < 256 -> 0 <= R -> Z.lor a (Z.shiftl R 8) = a + 256 * R.
Proof.
intros a R Ha HR.
assert (L0 : Z.land a (Z.shiftl R 8) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases n 8) as [L|G]; [rewrite Z.shiftl_spec_low by lia; apply andb_false_r|].
destruct (Z.eq_dec a 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
rewrite (Z.bits_above_log2 a n); [reflexivity| lia|]. apply Z.lt_le_trans with 8; [|exact G]. apply Z.log2_lt_pow2; [lia|]. change (2^8) with 256. lia. }
rewrite <- Z.lxor_lor by exact L0. rewrite <- Z.add_nocarry_lxor by exact L0. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. lia.
Qed.
Lemma bytes_le_to_Z_bound_h : forall bs, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
induction bs as [|b bs IH]; [cbn; lia|].
cbn [bytes_le_to_Z length]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
replace (8 * Z.of_nat (S (length bs))) with (8 * Z.of_nat (length bs) + 8) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256. rewrite lor_byte_shift_h by lia. nia.
Qed.
Lemma Z_to_le_bytes_of_bytes_h : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [bytes_le_to_Z length Z_to_le_bytes]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
pose proof (bytes_le_to_Z_bound_h bs) as B. rewrite lor_byte_shift_h by lia. f_equal.
- apply zb8_eq. replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs); [exact IH|].
apply Z.div_unique with (r := bv_unsigned b); [left; lia| lia].
Qed.
Lemma le8_of_bytes_h : forall j : list byte, length j = 8%nat -> le8 (le_bytes_to_word j) = j.
Proof.
intros j L. unfold le8, word_to_le_bytes, le_bytes_to_word.
pose proof (bytes_le_to_Z_bound_h j) as B. rewrite L in B. change (8 * Z.of_nat 8) with 64 in B.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small by lia.
rewrite <- L at 1. apply Z_to_le_bytes_of_bytes_h.
Qed.
Lemma CB_C8s_h : forall n (j : list byte), length j = (8 * n)%nat -> exists ws : list word, length ws = n /\ cells_bytes (map C8 ws) = j.
Proof.
induction n as [|n IH]; intros j L.
- exists []. split; [reflexivity|]. destruct j; [reflexivity| cbn in L; lia].
- destruct (IH (skipn 8 j)) as (ws & Lws & E); [rewrite length_skipn; lia|].
exists (le_bytes_to_word (firstn 8 j) :: ws). split; [cbn; lia|].
cbn [map cells_bytes cbytes]. rewrite E, le8_of_bytes_h by (rewrite length_firstn; lia). apply firstn_skipn.
Qed.
Lemma cells_wf_C8s_h : forall ws : list word, cells_wf (map C8 ws).
Proof. induction ws; cbn; auto. Qed.

Lemma hsp_of_CB : forall (m : word -> option byte) A js, rw_cells asegs m A [CB 216 js] ->
exists w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208,
rw_cells asegs m A (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208).
Proof.
intros m A js H.
assert (L : length js = (8 * 27)%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
destruct (CB_C8s_h 27 js L) as (ws & Lws & E).
destruct ws as [|w0 [|w8 [|w16 [|w24 [|w32 [|w40 [|w48 [|w56 [|w64 [|w72 [|w80 [|w88 [|w96 [|w104 [|w112 [|w120 [|w128 [|w136 [|w144 [|w152 [|w160 [|w168 [|w176 [|w184 [|w192 [|w200 [|w208 [|? ?]]]]]]]]]]]]]]]]]]]]]]]]]]]]; try discriminate Lws.
exists w0, w8, w16, w24, w32, w40, w48, w56, w64, w72, w80, w88, w96, w104, w112, w120, w128, w136, w144, w152, w160, w168, w176, w184, w192, w200, w208.
eapply rw_cells_recast; [exact H| apply (cells_wf_C8s_h [w0; w8; w16; w24; w32; w40; w48; w56; w64; w72; w80; w88; w96; w104; w112; w120; w128; w136; w144; w152; w160; w168; w176; w184; w192; w200; w208])|]. cbn [cells_bytes cbytes app] in *. rewrite app_nil_r. exact E.
Qed.

Definition HSH_P1 : list byte := map (Z_to_bv 8) [-15; -15; -15; -15; -8; -14; -8; -8; -8; -8; -8; -14; -14; -14; -14; -14].
Definition HSH_L_HDR : list byte := map (Z_to_bv 8) [-15; -15; -15; -15; 4; -14; 0; 0; 0; 0; 0; -14; -14; -14; -14; -14].
Definition HSH_P2 : list byte := map (Z_to_bv 8) (zruns [(-14, 32%nat); (-8, 1%nat); (-14, 1%nat); (-8, 6%nat); (-14, 4%nat); (-8, 4%nat); (-14, 4%nat); (-8, 4%nat);
(-14, 4%nat); (-8, 6%nat); (-14, 4%nat); (-8, 51%nat); (-14, 9%nat); (-8, 3%nat); (-14, 5%nat); (-8, 1%nat); (-14, 1%nat); (-8, 1%nat); (-13, 3%nat)]).
Definition HSH_P3 : list byte := map (Z_to_bv 8) (zruns [(-14, 32%nat); (4, 1%nat); (-14, 1%nat); (0, 6%nat); (-14, 4%nat); (0, 4%nat); (-14, 4%nat); (0, 4%nat);
(-14, 4%nat); (0, 6%nat); (-14, 4%nat); (0, 51%nat); (-14, 9%nat); (0, 3%nat); (-14, 5%nat); (-8, 1%nat); (-14, 1%nat); (-8, 1%nat); (-13, 3%nat)]).
Definition HSH_T : list byte := map (Z_to_bv 8) (zruns [(-14, 32%nat); (4, 1%nat); (-14, 1%nat); (0, 6%nat); (-14, 4%nat); (0, 4%nat); (-14, 4%nat); (0, 4%nat);
(-14, 4%nat); (0, 6%nat); (-14, 4%nat); (0, 51%nat); (-14, 9%nat); (0, 3%nat); (-14, 5%nat); (4, 1%nat); (-14, 1%nat); (4, 1%nat); (-13, 3%nat)]).

Definition HSH_R : list byte := repeat (Z_to_bv 8 0) 1000 ++ HSH_T.
Definition HSH_MAIN : list byte := HSH_P1 ++ HSH_R.
Definition HSH_HDR : list byte := HSH_L_HDR ++ HSH_R.
Lemma HSH_MAIN_length : length HSH_MAIN = 1160%nat.  Proof. reflexivity. Qed.
Lemma HSH_HDR_length : length HSH_HDR = 1160%nat.  Proof. reflexivity. Qed.
Lemma HSH_R_length : length HSH_R = 1144%nat.  Proof. reflexivity. Qed.

Lemma hsh_slice_acc : forall (m : word -> option byte) (F : Z) (sh : list byte) (o n : Z),
F mod 8 = 0 -> 0 <= F -> o mod 8 = 0 -> 0 <= o -> 0 <= n ->
bytes_at asegs m (shad F) sh -> (Z.to_nat (o / 8) + length (ushadow n) <= length sh)%nat ->
firstn (length (ushadow n)) (skipn (Z.to_nat (o / 8)) sh) = ushadow n ->
acc asegs m (F + o) n.
Proof.
intros m F sh o n F8 F0 O8 O0 N0 B L E.
apply acc_ushadow; [rewrite Zplus_mod, F8, O8; reflexivity| lia| lia|].
rewrite (shad_aligned_add F o F8 O0).
pose proof (bytes_at_sub m (shad F) sh (Z.to_nat (o / 8)) (length (ushadow n)) B ltac:(lia)) as X.
rewrite E, Z2Nat.id in X by (apply Z.div_pos; lia). exact X.
Qed.

Lemma hsh_R_acc : forall (m : word -> option byte) (F : Z),
F mod 8 = 0 -> 0 <= F -> bytes_at asegs m (shad F + 16) HSH_R ->
acc asegs m (F + HO_OUT) 8000 /\ acc asegs m (F + HO_FSZ) 4 /\ acc asegs m (F + HO_BITS) BITS_SIZEOF /\ acc asegs m (F + HO_OY) 32
/\ acc asegs m (F + HO_OG) 32 /\ acc asegs m (F + HO_OP) 48 /\ acc asegs m (F + HO_OS) 408 /\ acc asegs m (F + HO_STEREO) 24
/\ acc asegs m (F + HO_RATE) 4 /\ acc asegs m (F + HO_LOOK) 4.
Proof.
intros m F F8 F0 B.
assert (B' : bytes_at asegs m (shad F) (repeat (Z_to_bv 8 0) 16 ++ HSH_R) -> True) by (intros; exact I).
clear B'.

assert (SL : forall o n, o mod 8 = 0 -> 128 <= o -> 0 <= n -> (Z.to_nat (o / 8 - 16) + length (ushadow n) <= length HSH_R)%nat ->
firstn (length (ushadow n)) (skipn (Z.to_nat (o / 8 - 16)) HSH_R) = ushadow n -> acc asegs m (F + o) n).
{ intros o n O8 O128 N0 L E.
apply acc_ushadow; [rewrite Zplus_mod, F8, O8; reflexivity| lia| lia|].
rewrite (shad_aligned_add F o F8 ltac:(lia)).
pose proof (bytes_at_sub m (shad F + 16) HSH_R (Z.to_nat (o / 8 - 16)) (length (ushadow n)) B L) as X.
rewrite E, Z2Nat.id in X by (apply Z.le_0_sub; apply Z.div_le_lower_bound; lia).
replace (shad F + o / 8) with (shad F + 16 + (o / 8 - 16)) by lia. exact X. }
unfold HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK, BITS_SIZEOF.
repeat split; (apply SL; [reflexivity| lia| lia| vm_compute; lia| vm_compute; reflexivity]).
Qed.

Lemma hsh_L_hdr_acc : forall (m : word -> option byte) (F : Z),
F mod 8 = 0 -> 0 <= F -> bytes_at asegs m (shad F) HSH_L_HDR ->
acc asegs m (F + HO_ENH) 4 /\ acc asegs m (F + HO_CBK) 40.
Proof.
intros m F F8 F0 B. unfold HO_ENH, HO_CBK.
split; (apply (hsh_slice_acc m F HSH_L_HDR); [exact F8| exact F0| reflexivity| lia| lia| exact B| vm_compute; lia| vm_compute; reflexivity]).
Qed.

Lemma rw_CB_cut : forall segs (m : word -> option byte) A (n k : nat) js, (k <= n)%nat -> rw_cells segs m A [CB n js] ->
exists j1 j2, rw_cells segs m A [CB k j1] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k) j2].
Proof.
intros segs m A n k js K H. apply (rw_cells_split_CB segs m A [] n js [] [k; n - k]%nat) in H; [| cbn; lia].
cbn [mk_CB_cells app] in H. apply (proj1 (rw_cells_app segs m A [CB k _] [CB (n - k) _])) in H. destruct H as (H1 & H2). cbn [cells_size csize] in H2.
do 2 eexists. split; [exact H1|]. rewrite Nat.add_0_r in H2. exact H2.
Qed.
Ltac cb_cut H k H1 :=
lazymatch type of H with rw_cells ?segs ?m ?A [CB ?n ?js] =>
let r := eval vm_compute in (n - k)%nat in
let zk := eval vm_compute in (Z.of_nat k) in
let j1 := fresh "j" in let j2 := fresh "j" in let H2 := fresh "H" in
destruct (rw_CB_cut segs m A n k js ltac:(apply Nat.leb_le; vm_compute; reflexivity) H) as (j1 & j2 & H1 & H2);
clear H; change (n - k)%nat with r in H2; change (Z.of_nat k) with zk in H2;
lazymatch A with
| (?B + ?c)%Z => let c' := eval vm_compute in (c + zk)%Z in replace (A + zk)%Z with (B + c')%Z in H2 by lia
| _ => idtac
end;
rename H2 into H
end.
