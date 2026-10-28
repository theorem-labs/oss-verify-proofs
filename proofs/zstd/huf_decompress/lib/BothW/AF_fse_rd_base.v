(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation zlen l := (Z.of_nat (length l)).
Ltac brute_regF n r lo cnt g :=
let w := getreg n in
lazymatch w with
| Z_to_bv 64 ?e =>
let F := eval pattern r in e in
lazymatch F with
| ?f r =>
let H := fresh "BR" in
assert (H : forall r0, lo <= r0 < lo + cnt -> (f r0 =? g r0) = true)
by (apply (brute_range (fun r0 => f r0 =? g r0) lo cnt); vm_compute; reflexivity);
replace e with (g r) by (symmetry; apply Z.eqb_eq; apply H; lia);
clear H
end
| _ => fail "brute_regF: register" n "holds" w
end.
Record rdctxA : Type := mkRDA {
a_gp : word; a_tp : word;
a_F : bvmap 5 word; a_fc : bv 32;
a_m : amem;
a_SP : Z; a_FF : Z; a_NC : Z; a_MSVP : Z; a_TLP : Z; a_BUF : Z; a_lo : Z;
a_rt0 : list Z; a_buf : list Z; a_msv0 : Z
}.
Definition a_SPA (C : rdctxA) : Z := (a_SP C - 192) - (a_SP C - 192) mod 32.
Lemma spaA_bounds : forall C, a_SP C mod 16 = 0 -> a_SP C - 208 <= a_SPA C <= a_SP C - 192 /\ a_SPA C mod 32 = 0.
Proof. intros C H. unfold a_SPA. Z.div_mod_to_equations.
lia. Qed.
Definition RDA_CALLEE : Z := 2224.
Definition ASHB : Z := 2147450880.
Definition rd_WA (C : rdctxA) : list (Z * Z) :=
[(a_NC C, a_NC C + 2 * zlen (a_rt0 C)); (a_MSVP C, a_MSVP C + 4); (a_TLP C, a_TLP C + 4); (a_SPA C - RDA_CALLEE, a_SPA C + 88)].
Section CANSEC1. Context {rc : runConstT}.
Definition rd_okA (C : rdctxA) : Prop :=
8 <= zlen (a_buf C) <= 65536 /\ Forall (fun c => 0 <= c < 256) (a_buf C)
/\ 0 <= a_msv0 C <= 255 /\ a_msv0 C + 1 <= zlen (a_rt0 C) /\ zlen (a_rt0 C) <= 65536
/\ a_SP C mod 16 = 0 /\ a_SP C + 16 < KEND /\ a_lo C <= a_SPA C - RDA_CALLEE /\ ATOP <= a_lo C
/\ ablk (a_NC C) (a_NC C + 2 * zlen (a_rt0 C)) /\ a_NC C mod 8 = 0
/\ ablk (a_MSVP C) (a_MSVP C + 4) /\ a_MSVP C mod 4 = 0
/\ ablk (a_TLP C) (a_TLP C + 4) /\ a_TLP C mod 4 = 0
/\ ablk (a_BUF C) (a_BUF C + zlen (a_buf C))
/\ ablk (a_FF C) (a_FF C + 64) /\ a_FF C mod 64 = 0
/\ (a_NC C + 2 * zlen (a_rt0 C) <= a_MSVP C \/ a_MSVP C + 4 <= a_NC C)
/\ (a_NC C + 2 * zlen (a_rt0 C) <= a_TLP C \/ a_TLP C + 4 <= a_NC C)
/\ (a_NC C + 2 * zlen (a_rt0 C) <= a_BUF C \/ a_BUF C + zlen (a_buf C) <= a_NC C)
/\ (a_MSVP C + 4 <= a_TLP C \/ a_TLP C + 4 <= a_MSVP C)
/\ (a_MSVP C + 4 <= a_BUF C \/ a_BUF C + zlen (a_buf C) <= a_MSVP C)
/\ (a_TLP C + 4 <= a_BUF C \/ a_BUF C + zlen (a_buf C) <= a_TLP C)
/\ 0 <= a_BUF C.
Definition rd_shA (C : rdctxA) : Prop :=
unpoisoned (a_m C) (a_NC C) (a_NC C + 2 * zlen (a_rt0 C)) /\ unpoisoned (a_m C) (a_MSVP C) (a_MSVP C + 4)
/\ unpoisoned (a_m C) (a_TLP C) (a_TLP C + 4) /\ unpoisoned (a_m C) (a_BUF C) (a_BUF C + zlen (a_buf C)).
Definition rd_rngA (C : rdctxA) (RNG : footprint) : Prop :=
rng_aimg RNG /\ rng RNG (a_lo C) (a_SP C - a_lo C)
/\ rng RNG (a_NC C) (2 * zlen (a_rt0 C)) /\ rng RNG (shad (a_NC C)) (nshad (2 * zlen (a_rt0 C)))
/\ rng RNG (a_MSVP C) 4 /\ rng RNG (shad (a_MSVP C)) 1
/\ rng RNG (a_TLP C) 4 /\ rng RNG (shad (a_TLP C)) 1
/\ rng RNG (a_BUF C) (zlen (a_buf C)) /\ rng RNG (shad (a_BUF C)) (nshad (zlen (a_buf C) + a_BUF C mod 8)).
Definition FRA_main (C : rdctxA) (j0 j64 : list byte) : list cell :=
[CB 8 j0; C8 (Z_to_bv 64 (a_BUF C + zlen (a_buf C) + -4)); C8 (Z_to_bv 64 (Z.shiftr (a_MSVP C) 3 + ASHB)); C8 (Z_to_bv 64 (a_FF C));
C8 (Z_to_bv 64 16843009); C8 (Z_to_bv 64 252645135); C8 (Z_to_bv 64 1431655765); C8 (Z_to_bv 64 (a_MSVP C));
CB 16 j64; C8 (Z_to_bv 64 (a_FF C))].
Definition rd_invA (C : rdctxA) (m1 : amem) (nc : list Z) (msvw tlw : word) : Prop :=
u8arr bsegs m1 (a_NC C) (u16s (map (Z_to_bv 64) nc)) /\ length nc = length (a_rt0 C)
/\ bytes_at bsegs m1 (a_BUF C) (map (Z_to_bv 8) (a_buf C))
/\ rw_cells bsegs m1 (a_MSVP C) [C4 msvw]
/\ rw_cells bsegs m1 (a_TLP C) [C4 tlw]
/\ (exists j0 j64, rw_cells bsegs m1 (a_SPA C) (FRA_main C j0 j64))
/\ stk bsegs m1 (a_lo C) (a_SPA C)
/\ munch (rd_WA C) (a_m C) m1 /\ wmono bsegs (a_m C) m1 /\ mem_inv bsegs m1.
#[using="Type"] Lemma inv_shadowA : forall C m1, rd_okA C -> rd_shA C -> munch (rd_WA C) (a_m C) m1 ->
unpoisoned m1 (a_NC C) (a_NC C + 2 * zlen (a_rt0 C)) /\ unpoisoned m1 (a_MSVP C) (a_MSVP C + 4)
/\ unpoisoned m1 (a_TLP C) (a_TLP C + 4) /\ unpoisoned m1 (a_BUF C) (a_BUF C + zlen (a_buf C)).
Proof.
intros C m1 OK (U1 & U2 & U3 & U4) MU.
destruct OK as (HH & _ & HM0 & HM1 & HN & SP16 & SPK & LO & LOA & BN & _ & BM & _ & BT & _ & BB & BF & _).
pose proof (ablk_lin _ _ BN) as LN. pose proof (ablk_lin _ _ BM) as LM. pose proof (ablk_lin _ _ BT) as LT. pose proof (ablk_lin _ _ BB) as LB.
pose proof (ablk_disj_band _ _ BN) as DN. pose proof (ablk_disj_band _ _ BM) as DM. pose proof (ablk_disj_band _ _ BT) as DT.
pose proof atop_range as ATR.
unfold rd_WA, RDA_CALLEE, a_SPA, KHIGH, KLS, KEND, AIMG_HI in *.
repeat split; (eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|];
split; [Z.div_mod_to_equations; lia| exact I]).
Qed.
#[using="Type"] Lemma okA_lin : forall C, rd_okA C ->
8 <= zlen (a_buf C) <= 65536 /\ 0 <= a_msv0 C <= 255 /\ a_msv0 C + 1 <= zlen (a_rt0 C) /\ zlen (a_rt0 C) <= 65536
/\ a_SP C mod 16 = 0 /\ a_SP C + 16 < KEND /\ a_lo C <= a_SPA C - RDA_CALLEE /\ ATOP <= a_lo C
/\ a_SP C - 208 <= a_SPA C <= a_SP C - 192 /\ a_SPA C mod 32 = 0
/\ AIMG_HI <= a_NC C /\ a_NC C + 2 * zlen (a_rt0 C) <= ATOP /\ a_NC C mod 8 = 0
/\ AIMG_HI <= a_MSVP C /\ a_MSVP C + 4 <= ATOP /\ a_MSVP C mod 4 = 0
/\ AIMG_HI <= a_TLP C /\ a_TLP C + 4 <= ATOP /\ a_TLP C mod 4 = 0
/\ AIMG_HI <= a_BUF C /\ a_BUF C + zlen (a_buf C) <= ATOP /\ 0 <= a_BUF C
/\ AIMG_HI <= a_FF C /\ a_FF C + 64 <= ATOP /\ a_FF C mod 64 = 0.
Proof.
intros C OK. pose proof OK as (HH & FBY & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & BN & N8 & BM & M4 & BT & T4 & BB & BF & F64 & _ & _ & _ & _ & _ & _ & B8).
pose proof (spaA_bounds C SP16) as [SPA1 SPA2].
apply ablk_lin in BN, BM, BT, BB, BF. unfold AIMG_HI in *.
lia.
Qed.
#[using="Type"] Lemma acc_shadowA : forall RNG A len a, rng RNG (shad A) (nshad len) -> A mod 8 = 0 -> (0 <= A /\ A <= a /\ a < A + len /\ A + len + 8 <= 2^47) ->
acc_in RNG (Z_to_bv 64 (Z.shiftr a 3 + 2147450880), 1%nat).
Proof.
intros RNG A len a (H0 & H1 & H) A8 (HA & Ha1 & Ha2 & HL). unfold acc_in. cbn [fst snd].
rewrite shad_div, nshad_div in *. unfold ASHOFF in *.
rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite unsigned_lit by (Z.div_mod_to_equations; lia).
apply H; Z.div_mod_to_equations; lia.
Qed.
#[using="Type"] Lemma acc_shadow1 : forall RNG A a, rng RNG (shad A) 1 -> (0 <= A /\ A <= a /\ a < A - A mod 8 + 8 /\ A + 8 <= 2^47) ->
acc_in RNG (Z_to_bv 64 (Z.shiftr a 3 + 2147450880), 1%nat).
Proof.
intros RNG A a (H0 & H1 & H) (HA & Ha1 & Ha2 & HL). unfold acc_in. cbn [fst snd].
rewrite shad_div in *. unfold ASHOFF in *.
rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite unsigned_lit by (Z.div_mod_to_equations; lia).
apply H; Z.div_mod_to_equations; lia.
Qed.
#[using="Type"] Lemma acc_shadowU : forall RNG A len a, rng RNG (shad A) (nshad (len + A mod 8)) ->
(0 <= A /\ A <= a /\ a < A + len /\ A + len + 8 <= 2^47) ->
acc_in RNG (Z_to_bv 64 (Z.shiftr a 3 + 2147450880), 1%nat).
Proof.
intros RNG A len a (H0 & H1 & H) (HA & Ha1 & Ha2 & HL). unfold acc_in. cbn [fst snd].
rewrite shad_div, nshad_div in *. unfold ASHOFF in *.
rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite unsigned_lit by (Z.div_mod_to_equations; lia).
apply H; Z.div_mod_to_equations; lia.
Qed.
#[using="Type"] Lemma rd_invA_store2 : forall C m1 nc msvw tlw cn v, rd_okA C -> rd_invA C m1 nc msvw tlw -> 0 <= cn < zlen (a_rt0 C) ->
rd_invA C (write_to_mem m1 (wa (a_NC C + 2 * cn)) (le2 (Z_to_bv 64 v))) (Zupd cn (to_short v) nc) msvw tlw.
Proof.
intros C m1 nc msvw tlw cn v OK (ARR & LNC & HBUF & HMSV & HTL & (j0 & j64 & FR) & ST & MU & WM & MI) Hcn.
pose proof OK as (HH & FBY & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & BN & N8 & BM & M4 & BT & T4 & BB & BF & F64
& SNM & SNT & SNB & SMT & SMB & STB & B8).
pose proof (spaA_bounds C SP16) as [[SPA1 SPA2] SPA3].
apply ablk_lin in BN, BM, BT, BB, BF. pose proof atop_range as ATR. unfold AIMG_HI, RDA_CALLEE, FRA_main in *.
assert (LWS : length (map (Z_to_bv 64) nc) = length (a_rt0 C)) by (rewrite length_map; exact LNC).
pose proof (u16arr_store_ok bsegs _ (a_NC C) _ cn (wa (a_NC C + 2 * cn)) ARR ltac:(rewrite LWS; lia) eq_refl) as SOK.
pose proof (u16arr_write bsegs _ (a_NC C) _ cn (Z_to_bv 64 v) ARR ltac:(rewrite LWS; lia)) as ARR2.
rewrite u16s_upd_short in ARR2.
assert (L2 : length (le2 (Z_to_bv 64 v)) = 2%nat) by reflexivity.
unfold rd_invA. split; [exact ARR2|]. split; [unfold Zupd; rewrite upd_nat_length; exact LNC|].
split; [apply bytes_at_write_other; [exact HBUF| lia| rewrite L2; lia| rewrite L2, length_map; lia]|].
split; [apply rw_cells_frame; [exact HMSV| lia| rewrite L2; lia| rewrite L2; cbn; lia]|].
split; [apply rw_cells_frame; [exact HTL| lia| rewrite L2; lia| rewrite L2; cbn; lia]|].
split; [exists j0, j64; apply rw_cells_frame; [exact FR| lia| rewrite L2; lia| rewrite L2; cbn; lia]|].
split; [apply stk_write; [exact ST| lia| rewrite L2; lia]|].
split; [apply munch_write; [exact MU| lia| rewrite L2; lia| unfold rd_WA; cbn [inside]; rewrite L2; lia]|].
split; [apply wmono_write; exact WM|].
apply mem_inv_store; [exact MI| rewrite L2; exact SOK].
Qed.
#[using="Type"] Lemma rd_invA_storeM : forall C m1 nc msvw tlw v, rd_okA C -> rd_invA C m1 nc msvw tlw ->
rd_invA C (write_to_mem m1 (wa (a_MSVP C)) (le4 (Z_to_bv 64 v))) nc (Z_to_bv 64 v) tlw.
Proof.
intros C m1 nc msvw tlw v OK (ARR & LNC & HBUF & HMSV & HTL & (j0 & j64 & FR) & ST & MU & WM & MI).
pose proof OK as (HH & FBY & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & BN & N8 & BM & M4 & BT & T4 & BB & BF & F64
& SNM & SNT & SNB & SMT & SMB & STB & B8).
pose proof (spaA_bounds C SP16) as [[SPA1 SPA2] SPA3].
apply ablk_lin in BN, BM, BT, BB, BF. pose proof atop_range as ATR. unfold AIMG_HI, RDA_CALLEE, FRA_main in *.
assert (L4 : length (le4 (Z_to_bv 64 v)) = 4%nat) by reflexivity.
pose proof (rw_cells_store_ok bsegs m1 (a_MSVP C) [C4 msvw] 0 (C4 msvw) 4 HMSV eq_refl eq_refl) as SOK.
cbn [Z.of_nat] in SOK. rewrite Z.add_0_r in SOK.
unfold rd_invA.
split; [apply u8arr_frame; [exact ARR| lia| rewrite L4; lia| rewrite L4, u16s_length, length_map; lia]|].
split; [exact LNC|].
split; [apply bytes_at_write_other; [exact HBUF| lia| rewrite L4; lia| rewrite L4, length_map; lia]|].
split.
{ pose proof (rw_cells_write bsegs m1 (a_MSVP C) [C4 msvw] 0 (C4 msvw) (C4 (Z_to_bv 64 v)) HMSV eq_refl eq_refl ltac:(cbn; auto)) as W.
cbn [Z.of_nat] in W. rewrite Z.add_0_r in W. exact W. }
split; [apply rw_cells_frame; [exact HTL| lia| rewrite L4; lia| rewrite L4; cbn; lia]|].
split; [exists j0, j64; apply rw_cells_frame; [exact FR| lia| rewrite L4; lia| rewrite L4; cbn; lia]|].
split; [apply stk_write; [exact ST| lia| rewrite L4; lia]|].
split; [apply munch_write; [exact MU| lia| rewrite L4; lia| unfold rd_WA; cbn [inside]; rewrite L4; lia]|].
split; [apply wmono_write; exact WM|].
apply mem_inv_store; [exact MI| rewrite L4; exact SOK].
Qed.
#[using="Type"] Lemma chk1A : forall m1 A B a N, unpoisoned m1 A B -> A <= a -> a + N <= B -> 1 <= N -> a mod 8 + N <= 8 ->
exists b, ov_read_bytes bsegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
/\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 + N - 1 < sval b)) /\ -128 <= sval b <= 127.
Proof.
intros m1 A B a N U A0 A1 N1 N8.
destruct (unpoisoned_check_rd bsegs m1 A B a N U A0 A1 N1 N8) as (b & RDB & CK).
exists b. unfold shad, ASHOFF in RDB.
replace (2147450880 + Z.shiftr a 3) with (Z.shiftr a 3 + 2147450880) in RDB by lia.
split; [exact RDB|]. split; [exact CK| apply sval_range].
Qed.
#[using="Type"] Lemma chkB : forall m1 A B a, unpoisoned m1 A B -> A <= a -> a + 1 <= B ->
exists b, ov_read_bytes bsegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
/\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 < sval b)) /\ -128 <= sval b <= 127.
Proof.
intros m1 A B a U A0 A1.
pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as M8.
destruct (chk1A m1 A B a 1 U A0 A1 ltac:(lia) ltac:(lia)) as (b & RDB & CK & SR).
exists b. split; [exact RDB|]. split; [| exact SR]. destruct CK as [CK|CK]; [left; exact CK| right; lia].
Qed.
Definition rd_lstA (C : rdctxA) (pc : Z) (m1 : amem) (x1 x6 x7 x10 x11 x12 x13 x16 x18 x20 x22 x29 : word) : machine_state :=
MS (mkR x1 (Z_to_bv 64 (a_SPA C)) (a_gp C) (a_tp C)
(Z_to_bv 64 1) x6 x7
(Z_to_bv 64 (a_SP C)) (Z_to_bv 64 (a_SPA C)) x10 x11 x12 x13
(Z_to_bv 64 (a_BUF C + zlen (a_buf C) + -7)) (Z_to_bv 64 858993459) x16 (Z_to_bv 64 4)
x18 (Z_to_bv 64 (a_BUF C + zlen (a_buf C))) x20 (Z_to_bv 64 (a_NC C)) x22 (Z_to_bv 64 (a_msv0 C + 1))
(Z_to_bv 64 2147450880) (Z_to_bv 64 (a_FF C)) (Z_to_bv 64 (Z.shiftr (a_FF C) 3 + 2147450880)) (Z_to_bv 64 (a_BUF C))
(Z_to_bv 64 18446744071562067968) x29 (Z_to_bv 64 23) (Z_to_bv 64 125613361))
(a_F C) (Z_to_bv 64 pc) (a_fc C) None m1 (seg_rom bsegs).
Definition rd_headA (C : rdctxA) (s : rstate) (m1 : amem) (x7 x12 x20 x22 x29 : word) : machine_state :=
rd_lstA C (if r_previous0 s then 0x96cf8 else 0x96cdc) m1 (Z_to_bv 64 (r_nbBits s)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s))) x7
(Z_to_bv 64 (a_BUF C + r_ip s)) (Z_to_bv 64 (r_remaining s)) x12 (Z_to_bv 64 (r_charnum s))
(Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (r_threshold s)) x20 x22 x29.
Definition rd_cntA (C : rdctxA) (s : rstate) (m1 : amem) (x7 x10 x22 : word) : machine_state :=
rd_lstA C 0x96ecc m1 (Z_to_bv 64 (r_nbBits s)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s))) x7
x10 (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (a_BUF C + r_ip s)) (Z_to_bv 64 (r_charnum s))
(Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (r_threshold s))
(Z_to_bv 64 (r_threshold s * 2 + -1 - r_remaining s)) x22 (Z_to_bv 64 (r_threshold s * 2 + -1)).
Definition rd_exitA (C : rdctxA) (s : rstate) (m1 : amem) (x1 x6 x7 x12 x18 x20 x22 x29 : word) : machine_state :=
rd_lstA C 0x97190 m1 x1 x6 x7 (Z_to_bv 64 (a_BUF C + r_ip s)) (Z_to_bv 64 (r_remaining s)) x12 (Z_to_bv 64 (r_charnum s))
(Z_to_bv 64 (r_bitCount s)) x18 x20 x22 x29.
Definition rd_brk_okA (C : rdctxA) (s : rstate) : Prop :=
0 <= r_remaining s < 2^31 /\ 0 <= r_bitCount s < 2^31 /\ 0 <= r_charnum s < 2^31 /\ 0 <= r_ip s /\ r_ip s + 4 <= zlen (a_buf C).
Section Base.
Variable C : rdctxA.
Hypothesis OK : rd_okA C.
#[using="rc OK"] Lemma buf_rdA : forall m1 i, bytes_at bsegs m1 (a_BUF C) (map (Z_to_bv 8) (a_buf C)) -> 0 <= i < zlen (a_buf C) ->
ov_read_bytes bsegs m1 (Z_to_bv 64 (a_BUF C + i)) 1 = Some [Z_to_bv 8 (Znth i (a_buf C))] /\ 0 <= Znth i (a_buf C) < 256.
Proof.
intros m1 i HB Hi. destruct OK as (_ & FB & _). unfold Znth.
assert (L : (Z.to_nat i < length (a_buf C))%nat) by lia.
split.
- eapply (u8ro_read bsegs m1 (a_BUF C) _ i); [exact HB| | lia| unfold wa; f_equal; lia].
rewrite nth_error_map. rewrite (nth_error_nth' (a_buf C) 0 L). reflexivity.
- apply (proj1 (Forall_forall _ _) FB). apply nth_In. exact L.
Qed.
#[using="rc OK"] Lemma buf_all_bytesA : all_bytes (a_buf C).
Proof. destruct OK as (_ & FB & _). apply Forall_all_bytes. exact FB. Qed.
End Base.
End CANSEC1.
Ltac rdA_acc_hint :=
lazymatch goal with
| |- acc_in ?R (Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880), 1%nat) =>
let X := leftmost a in
match goal with
| H : rng R (shad ?A) (nshad (?len + ?A' mod 8)) |- _ => constr_eq X A; constr_eq A A'; apply (acc_shadowU R A len a H); lia
| H : rng R (shad ?A) (nshad ?len) |- _ => constr_eq X A; apply (acc_shadowA R A len a H); [lia| lia]
| H : rng R (shad ?A) 1 |- _ => constr_eq X A; apply (acc_shadow1 R A a H); lia
end
| |- acc_in ?R (Z_to_bv 64 (a_SPA ?C + _), _) => match goal with H : rng R (a_lo C) _ |- _ => solve_acc_with H end
| |- acc_in ?R (Z_to_bv 64 (a_SPA ?C), _) => match goal with H : rng R (a_lo C) _ |- _ => solve_acc_with H end
end.
