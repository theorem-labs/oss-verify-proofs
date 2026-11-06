(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 1005 of its 1043 lines of code are new or changed and 507 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i YCbf YCj1 YCjr YCja YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntSeat DiscoYEntProCuts DiscoYEntProSeat DiscoYEntShChk.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition pb_srf (u o : Z) (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0 | 19%nat => SOff 32 0
  | 10%nat => SLit u | 11%nat => SLit 1 | 12%nat => SOff AT_F o | 22%nat => SOff AT_F 0 | 24%nat => SOff AT_F 0
  | _ => SOff (AT_X + r) 0
  end.
Definition pb_sr (u o : Z) : list sv := map (pb_srf u o) (seq 0 32).
Definition pb_vals (regs : bvmap 5 word) (xs : list word) : list word :=
  map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) ++ xs.
Definition pb_xs (pl : list byte) (i : Z) (k : nat) : list word :=
  map (fun j => Z_to_bv 64 (rdb pl (Z.to_nat i + j))) (seq 0 k).
Definition pb_inr (k : nat) : list YP09.region :=
  match k with
  | O => []
  | _ => [YP09.mkRegion (Some 552%nat) 0 (Z.of_nat k) 0 0
           (firstn k [YP09.mkChunk 0 (CVal 1 (SOff 563 0)); YP09.mkChunk 1 (CVal 1 (SOff 564 0))])]
  end.
Definition pb_fa (k : nat) : list (nat * afact) :=
  match k with
  | O => []
  | _ => (552%nat, mkAF 4096 140737479966720 0) :: firstn k [(563%nat, mkAF 0 255 0); (564%nat, mkAF 0 255 0)]
  end.
Definition PBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition PBspan0 : Z * Z := (0, 0).
Definition pb_cell_region (q : nat) (s : Z) : YP09.region :=
  YP09.mkRegion (Some q) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit s))].
Lemma region_ok_narrow : forall segs E m r wlo whi, region_ok segs E m r ->
  YP09.r_wlo r <= wlo -> whi <= YP09.r_whi r -> region_ok segs E m (set_window r wlo whi).
Proof.
intros segs E m r wlo whi H H1 H2. apply region_ok_rewindow; [exact H|].
intros o Ho. destruct H as (_ & _ & Hw & _). apply Hw. lia.
Qed.

Lemma pb_branch : forall E m v c, ew E m = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff m c)) (sv_denot E (SLit 0)) = negb (v + c =? 0) /\
  branch_taken BC_EQ (sv_denot E (SOff m c)) (sv_denot E (SLit 0)) = (v + c =? 0).
Proof.
intros E m v c Hm Hv Hc. rewrite branch_ne_U, branch_eq_U, U_SOff, U_lit by lia.
unfold w64 in Hm. rewrite Hm, unsigned_lit_small by lia. rewrite zcanon_id by (unfold M64; lia). auto.
Qed.

Lemma pb_U : forall E m v c, ew E m = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> U E (SOff m c) = v + c.
Proof.
intros E m v c Hm Hv Hc. rewrite U_SOff. unfold w64 in Hm. rewrite Hm, unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.

Lemma pb_rdb_lt : forall pl j, 0 <= rdb pl j < 256.
Proof.
intros pl j. unfold rdb. pose proof (bv_unsigned_in_range 8 (nth j pl (Z_to_bv 8 0))) as H.
change (bv_modulus 8) with 256 in H. lia.
Qed.

Lemma pb_rdb_out : forall pl j, (length pl <= j)%nat -> rdb pl j = 0.
Proof. intros pl j Hj. unfold rdb. rewrite nth_overflow by exact Hj. reflexivity. Qed.

Lemma pb_byte0 : 0 <= 0 < 256.
Proof. lia. Qed.

Lemma pb_xs_nth : forall pl i k j, (j < k)%nat ->
  nth j (pb_xs pl i k) (Z_to_bv 64 0) = Z_to_bv 64 (rdb pl (Z.to_nat i + j)).
Proof.
intros pl i k j Hj. unfold pb_xs.
pose proof (map_nth (fun j0 => Z_to_bv 64 (rdb pl (Z.to_nat i + j0))) (seq 0 k) 0%nat j) as Hm. cbv beta in Hm.
rewrite seq_nth in Hm by exact Hj. rewrite Nat.add_0_l in Hm. rewrite <- Hm. apply nth_indep. rewrite length_map, length_seq. exact Hj.
Qed.

Lemma pb_xs_len : forall pl i k, length (pb_xs pl i k) = k.
Proof. intros. unfold pb_xs. rewrite length_map, length_seq. reflexivity. Qed.

Lemma pb_val_aview : forall {segs : list Segment} H (m : word -> option byte) a v,
  aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros segs H m a v Hv kk Hk. assert (kk = 0%nat) as -> by lia. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:Hb; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite !(Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.
Lemma pb_and7 : forall E m v c, ew E m = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  U E (SAlu ALU_AND (SOff m c) (SLit 7)) = (v + c) mod 8.
Proof.
intros E m v c Hm Hv Hc. rewrite U_and_lit by lia. rewrite (pb_U E m v c Hm Hv Hc).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma pb_ge_small : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof.
intros x y Hx Hy. rewrite YO0c.branch_ge. rewrite !unsigned_lit_small by lia. rewrite !YO0b.s64_small by lia. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Lemma pb_env_r : forall cx E regs xs r, (r < 32)%nat ->
  ew (d_env cx E (pb_vals regs xs)) (AT_X + r) = getr regs (Z_to_bv 5 (Z.of_nat r)).
Proof.
intros cx E regs xs r Hr. rewrite d_env_x by (unfold pb_vals; rewrite length_app, length_map, length_seq; lia).
unfold pb_vals. rewrite app_nth1 by (rewrite length_map, length_seq; exact Hr).
pose proof (map_nth (fun r0 => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32) 0%nat r) as Hm. cbv beta in Hm.
rewrite seq_nth in Hm by exact Hr. rewrite Nat.add_0_l in Hm. rewrite <- Hm. apply nth_indep. rewrite length_map, length_seq. exact Hr.
Qed.

Lemma pb_env_x : forall cx E regs xs j, (j < length xs)%nat ->
  ew (d_env cx E (pb_vals regs xs)) (AT_X + 32 + j) = nth j xs (Z_to_bv 64 0).
Proof.
intros cx E regs xs j Hj. replace (AT_X + 32 + j)%nat with (AT_X + (32 + j))%nat by lia.
rewrite d_env_x by (unfold pb_vals; rewrite length_app, length_map, length_seq; lia).
unfold pb_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq. f_equal. lia.
Qed.

Lemma d_E_agree : forall cx E E', (forall m, (m < AT_FL)%nat -> ew E' m = ew E m) -> d_E cx E -> d_E cx E'.
Proof.
intros cx E E' HA (EE & E32 & HEI & E60 & EF & ESH). unfold d_E.
assert (Hr : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E' n = getr (c_regs cx) r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hb. change (bv_modulus 5) with 32 in Hb.
  rewrite HA by (unfold AT_FL; lia). exact (EE n r Hn). }
split; [exact Hr|]. split; [rewrite HA by (unfold AT_FL; lia); exact E32|].
split; [intros a Ha; rewrite HA by (unfold A_LIM, AT_FL in *; lia); exact (HEI a Ha)|].
split; [rewrite HA by (unfold AT_FL, AT_A; lia); exact E60|].
split; [rewrite HA by (unfold AT_FL, AT_F; lia); exact EF|].
rewrite HA by (unfold AT_FL, AT_SH; lia); exact ESH.
Qed.

Lemma pb_val_of_ss : forall {fq : YK11.FPState} E ss (ms : machine_state) (H : word -> bool) n r off e v,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  nth_error (ss_mem ss) n = Some r ->
  In (YP09.mkChunk off (CVal 1 e)) (YP09.r_chunks r) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 ->
  val_mem SEGS (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) 1 v.
Proof.
intros fq E ss ms H n r off e v HS Hn Hin He Hv.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) n r HS Hn) as (_ & _ & _ & HC).
pose proof (proj1 (Forall_forall _ _) HC _ Hin) as Hc.
exact (val_of_chunk_ok _ E _ _ off 1 e v Hc He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

Lemma pb_pres_step : forall (H : word -> bool) (m1 m2 : word -> option byte) (P : Z -> Prop),
  mem_grows (mrestrict H m1) (mrestrict H m2) -> (forall a, P a -> apresent H m1 a) -> forall a, P a -> apresent H m2 a.
Proof. intros H m1 m2 P HG Hp a Ha. exact (apresent_grows H m1 m2 a HG (Hp a Ha)). Qed.

Lemma pb_mem_step : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  (forall a, 0 <= a < 2 ^ 64 -> in_wrange E rs a -> ~ P a) ->
  (forall a, 0 <= a < 2 ^ 64 -> P a -> aview SEGS H m1 a = aview SEGS H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> P a -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros E rs H m0 m1 m2 P HF Hw Hm a Ha Hp. rewrite <- (Hm a Ha Hp). apply aview_eq_of.
apply HF. rewrite unsigned_lit_small by lia. intros Hi. exact (Hw a Ha Hi Hp).
Qed.
Lemma pb_garr8_our : forall m a pl, (forall j, 0 <= j < 6 -> val_mem SEGS m (a + j) 1 (rdb pl (Z.to_nat j))) ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) (our_of pl)).
Proof.
intros m a pl H j Hj. unfold our_of in *. rewrite map_map in *. rewrite length_map, length_seq in Hj.
pose proof (map_nth (fun k => bv_unsigned (nth k pl (Z_to_bv 8 0))) (seq 0 6) 0%nat j) as Hm. cbv beta in Hm.
rewrite seq_nth in Hm by exact Hj. rewrite Nat.add_0_l in Hm.
rewrite (nth_indep _ 0 (bv_unsigned (nth 0 pl (Z_to_bv 8 0)))) by (rewrite length_map, length_seq; exact Hj).
rewrite Hm. fold (rdb pl j). split; [|apply pb_rdb_lt].
specialize (H (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id in H. exact H.
Qed.
Lemma pb_cell_region_ok : forall E (W : world SEGS) mem (q : nat) (y s : Z),
  ew E q = w64 y -> 0 <= y < 2 ^ 64 -> 0 <= s < 256 -> aview SEGS (w_H W) mem y = Some s ->
  region_ok SEGS E (mrestrict (w_H W) mem) (pb_cell_region q s).
Proof.
intros E W mem q y s Hq Hy Hs Hav. unfold w64 in Hq.
unfold region_ok, pb_cell_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hq, (unsigned_lit_small y) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS E _ y 0 1 (SLit s) s); [reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact (pb_val_aview (w_H W) mem y s Hav).
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.

Lemma regs_ok_pb : forall cx E regs (u o : Z) xs, d_E cx E -> p_rbase cx regs B ->
  getr regs 22 = w64 (d_FB cx) -> getr regs 24 = w64 (d_FB cx) ->
  getr regs 10 = w64 u -> getr regs 11 = w64 1 -> getr regs 12 = w64 (d_FB cx + o) ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx < 2 ^ 64 ->
  regs_ok (d_env cx E (pb_vals regs xs)) (pb_sr u o) regs.
Proof.
intros cx E regs u o xs HE HL H22 H24 H10 H11 H12 HA HFB.
pose proof HE as (HER & H32 & _ & HA60 & HF516 & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H27).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60. change AT_F with 516%nat in HF516.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot].
all: first
  [ rewrite getr_zero; reflexivity
  | rewrite H10; reflexivity | rewrite H11; reflexivity
  | unfold d_env; rewrite ew_havoc_old by (cbv; lia); rewrite HF516;
    first [ rewrite H12 | rewrite H22 | rewrite H24 ]; unfold w64;
    rewrite (unsigned_lit_small (d_FB cx)) by exact HFB; rewrite ?Z.add_0_r; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H19 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth pb_vals map seq Nat.add AT_X AT_FL app];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ].
Qed.
Lemma pb_base_in : forall cx, d_base B MT XM_LIB RLO RHI tfib_K cx ->
  c_n cx = Z.of_nat (length (c_pl cx)) /\
  (0 < c_n cx -> c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx))) /\
  garr8 SEGS (rd (c_W cx) (c_mem cx)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)).
Proof.
intros cx ((_ & _ & _ & _ & Hpn & Hlen & Harr & _) & _).
split; [exact Hlen|]. split; [|exact Harr]. intros Hn.
destruct Hpn as [[Hz _]|[H1 H2]]; [lia | split; [lia | exact H2]].
Qed.

Lemma pb_in_val : forall cx ly3 S3 (W : world SEGS) mem3 md3 kk j,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 kk ->
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) -> 0 <= j < c_n cx ->
  val_mem SEGS (rd W mem3) (c_p cx + j) 1 (rdb (c_pl cx) (Z.to_nat j)).
Proof.
intros cx ly3 S3 W mem3 md3 kk j HC Hab Hj.
pose proof HC as (Hbase & HJ & _).
destruct (pb_base_in cx Hbase) as (Hlen & Hin & Harr).
destruct (Hin ltac:(lia)) as (_ & Hin0).
assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (rewrite Hab; exact Hin0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hin3) as (_ & Hp4096 & _).
assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
destruct (garr8_nthZ SEGS _ _ _ j Harr ltac:(lia) ltac:(rewrite length_map; lia)) as (Hv & _).
assert (Hnth : nth (Z.to_nat j) (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0 = rdb (c_pl cx) (Z.to_nat j)).
{ unfold rdb. rewrite <- (map_nth (fun b : byte => bv_unsigned b) (c_pl cx) (Z_to_bv 8 0)).
  apply nth_indep. rewrite length_map. lia. }
rewrite Hnth in Hv.
refine (val_mem_entry_block SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hin0 Hin3 _ _ _ Hv); [lia | cbn; lia |].
intros x Hx (r & Hr & Hx2). destruct Hr.
Qed.

Lemma pb_addr : forall ly S (W : world SEGS) mem md p n x len,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= x -> x + len <= p + n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x len.
Proof.
intros ly S W mem md p n x len HAR Hin Hx Hxl y Hy.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (H16 & H4096 & _ & _ & _ & _ & Hn).
exists (dsh_cell p n y). split.
- unfold shadow_of_addr. exact (dsh_cell_val B LAWS ly S W mem md p n y HAR Hin ltac:(lia)).
- unfold saddr_ok. pose proof (dsh_cell_range p n y) as Hr.
  destruct (Z.eq_dec (dsh_cell p n y) 0) as [He|Hne]; [left; exact He|].
  right. split; [apply dsh_cell_lt; [lia | lia | lia | exact Hne] | lia].
Qed.
Lemma pb_seat : forall (fq : YK11.FPState) cx (u o m : Z) (k : nat) ys (W : world SEGS) ly3 S3 regs mem3 md3 kk E,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 kk -> d_E cx E ->
  Forall (region_ok SEGS E (rd W mem3)) (p_regions dsh_our ps_C2) ->
  rdword (aview SEGS (w_H W) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  regs_ok (d_env cx E (pb_vals regs (pb_xs (c_pl cx) m k ++ ys))) (pb_sr u o) regs ->
  getr regs 21 = w64 (c_p cx + m) -> ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ->
  0 <= m -> (k = 0%nat \/ ((k = 1 \/ k = 2)%nat /\ m + Z.of_nat k <= c_n cx)) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (pb_vals regs (pb_xs (c_pl cx) m k ++ ys)))
    (ss_p POFF_C2 (pb_sr u o) dsh_our (ps_C2 ++ []) [] (pb_inr k) (d_facts (pb_fa k) []))
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + POFF_C2)) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx u o m k ys W ly3 S3 regs mem3 md3 kk E HC HE HRG HFL Hregs H21 Hab Hm Hk.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (HFr : 0 <= d_FB cx < 2 ^ 64) by lia.
destruct Hk as [-> | (Hk12 & Hik)].
{ exact (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_our ps_C2 ly3 S3 W regs mem3 md3 kk E POFF_C2 (pb_sr u o) _ [] [] [] (d_facts [] [])
    HC HE HRG HFL Hregs (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 kk E _ [] [] HC HE I I)
    (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)). }
pose proof HC as (Hbase & HJ & Hfrs).
destruct (pb_base_in cx Hbase) as (Hlen & Hin & _).
destruct (Hin ltac:(lia)) as (Hn26 & Hin0).
assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (rewrite Hab; exact Hin0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (Hp16 & Hp4096 & Hpc & Hpapp & _ & _ & Hn).
assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
rewrite Hrq in Hpc, Hpapp.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hin3 Hfin) as Hsep.
rewrite Efa, Hrq in Hsep. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR3 Hin3) as Hoi. rewrite Hrq in Hoi.
pose proof (pa_obj_img 0 ltac:(vm_compute; lia)) as HO0. pose proof (pa_obj_img 12 ltac:(vm_compute; lia)) as HO12.
unfold IMG_LO, IMG_TOP in HO0, HO12. unfold off_img, IMG_LO, IMG_TOP in Hoi.
set (xs := pb_xs (c_pl cx) m k ++ ys) in *.
set (E' := d_env cx E (pb_vals regs xs)) in *.
destruct (d_E_env cx E (pb_vals regs xs) HE) as (EE & E32 & HEI & E60 & EF & ESH). fold E' in EE, E32, HEI, E60, EF, ESH.
assert (E552 : ew E' 552 = w64 (c_p cx + m)).
{ pose proof (pb_env_r cx E regs xs 21 ltac:(lia)) as X. change (AT_X + 21)%nat with 552%nat in X. fold E' in X. rewrite X. exact H21. }
assert (EX : forall j, (j < k)%nat -> ew E' (563 + j) = Z_to_bv 64 (rdb (c_pl cx) (Z.to_nat m + j))).
{ intros j Hj. pose proof (pb_env_x cx E regs xs j ltac:(unfold xs; rewrite length_app, pb_xs_len; lia)) as X.
  change (AT_X + 32 + j)%nat with (563 + j)%nat in X. fold E' in X. rewrite X. unfold xs.
  rewrite app_nth1 by (rewrite pb_xs_len; exact Hj). apply pb_xs_nth. exact Hj. }
assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
assert (Hd1 : d_FB cx / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
assert (U2 : base_val E' (Some AT_STK) = d_S cx).
{ cbn [base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
assert (U60 : base_val E' (Some AT_A) = d_A cx) by (cbn [base_val]; rewrite E60; apply unsigned_lit_small; exact HAr).
assert (U516 : base_val E' (Some AT_F) = d_FB cx) by (cbn [base_val]; rewrite EF; apply unsigned_lit_small; exact HFr).
assert (U529 : base_val E' (Some AT_SH) = shadow_addr (d_FB cx))
  by (cbn [base_val]; rewrite ESH; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (UG0 : base_val E' (Some (A_OBJ 0)) = VAL (A_OBJ 0)).
{ cbn [base_val]. rewrite (img_env_atomP E' (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  apply unsigned_lit_small. apply pa_val_range. }
assert (UG12 : base_val E' (Some (A_OBJ 12)) = VAL (A_OBJ 12)).
{ cbn [base_val]. rewrite (img_env_atomP E' (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  apply unsigned_lit_small. apply pa_val_range. }
assert (U552 : base_val E' (Some 552%nat) = c_p cx + m)
  by (cbn [base_val]; rewrite E552; unfold w64; apply unsigned_lit_small; lia).
assert (Hval : forall j, (j < k)%nat ->
  val_mem SEGS (rd W mem3) (c_p cx + m + Z.of_nat j) 1 (rdb (c_pl cx) (Z.to_nat m + j))).
{ intros j Hj. replace (Z.to_nat m + j)%nat with (Z.to_nat (m + Z.of_nat j)) by lia. rewrite <- Z.add_assoc.
  apply (pb_in_val cx ly3 S3 W mem3 md3 kk); [exact HC | exact Hab | lia]. }
assert (Hck : forall j, (j < k)%nat ->
  YP09.chunk_ok SEGS E' (rd W mem3) (c_p cx + m) (YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (563 + j) 0)))).
{ intros j Hj. apply (chunk_ok_val SEGS E' _ _ (Z.of_nat j) 1 _ (rdb (c_pl cx) (Z.to_nat m + j))).
  - cbn [sv_denot]. rewrite (EX j Hj), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (pb_rdb_lt (c_pl cx) (Z.to_nat m + j)). cbn. lia.
  - cbn. lia.
  - exact (Hval j Hj). }
assert (Hb : forall j, (j < k)%nat -> bv_unsigned (ew E' (563 + j)) = rdb (c_pl cx) (Z.to_nat m + j)).
{ intros j Hj. rewrite (EX j Hj). apply unsigned_lit_small. pose proof (pb_rdb_lt (c_pl cx) (Z.to_nat m + j)). lia. }
assert (Hat : atoms_ok E' (pb_fa k)).
{ destruct Hk12 as [-> | ->]; cbn [pb_fa firstn atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
  rewrite E552; unfold w64; rewrite unsigned_lit_small by lia;
  pose proof (Hb 0%nat ltac:(lia)) as B0; cbn [Nat.add] in B0; rewrite B0;
  pose proof (pb_rdb_lt (c_pl cx) (Z.to_nat m + 0)); rewrite Z.pow_0_r, ?Z.mod_1_r.
  - repeat split; lia.
  - pose proof (Hb 1%nat ltac:(lia)) as B1; cbn [Nat.add] in B1; rewrite B1.
    pose proof (pb_rdb_lt (c_pl cx) (Z.to_nat m + 1)). rewrite ?Z.mod_1_r. repeat split; lia. }
assert (Hreg : Forall (region_ok SEGS E' (rd W mem3)) (pb_inr k)).
{ destruct Hk12 as [-> | ->]; (apply Forall_cons; [|apply Forall_nil]); unfold region_ok; cbv zeta;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; rewrite U552;
  (split; [lia|]); (split; [cbn; lia|]); (split; [intros o0 Ho0; lia|]); cbn [firstn];
  repeat (apply Forall_cons; [first [exact (Hck 0%nat ltac:(lia)) | exact (Hck 1%nat ltac:(lia))]|]); apply Forall_nil. }
assert (Hpd : pairwise_disjoint E' (pb_inr k)) by (destruct Hk12 as [-> | ->]; split; exact I).
assert (Hdx : Forall (fun r => all_disjoint E' r (p_kregions dsh_our (ps_C2 ++ []) [])) (pb_inr k)).
{ destruct Hk12 as [-> | ->]; (apply Forall_cons; [|apply Forall_nil]);
  unfold p_kregions, fshadow_region, got_regionP, bcell_regionP; cbn [all_disjoint]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite U552, U2, U60, U516, U529, UG0, UG12;
  change (fs_frame_bytes DFRAME_CLASS / 8) with 512; change (fs_frame_bytes DFRAME_CLASS) with 4096;
  unfold shadow_addr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, MFRAME, LLVMF_STK in *;
  repeat split; lia. }
destruct Hk12 as [-> | ->].
- exact (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_our ps_C2 ly3 S3 W regs mem3 md3 kk E POFF_C2 (pb_sr u o) _ [] [] _ (d_facts _ [])
    HC HE HRG HFL Hregs (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 kk E _ _ [] HC HE Hat I)
    (Forall_nil _) (Forall_nil _) Hreg Hpd Hdx ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
- exact (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_our ps_C2 ly3 S3 W regs mem3 md3 kk E POFF_C2 (pb_sr u o) _ [] [] _ (d_facts _ [])
    HC HE HRG HFL Hregs (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 kk E _ _ [] HC HE Hat I)
    (Forall_nil _) (Forall_nil _) Hreg Hpd Hdx ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
Qed.

Definition pb_our (cx : dcx) (i : Z) (W : world SEGS) (mem : word -> option byte) : Prop :=
  forall j, 0 <= j < i -> val_mem SEGS (rd W mem) (d_obj cx OOUR + j) 1 (rdb (c_pl cx) (Z.to_nat j)).
Definition pb_inv (cx : dcx) (i : Z) : world SEGS -> config -> Prop :=
  d_at B MT XM_LIB RLO RHI tfib_K cx POFF_C2 0 0 (fun regs ly3 S3 W3 mem3 md3 =>
    p_canok cx /\ 0 <= i < 6 /\ p_rbase cx regs B /\ getr regs 22 = w64 (d_FB cx) /\ getr regs 24 = w64 (d_FB cx) /\
    getr regs 21 = w64 (c_p cx + Z.min i (c_n cx)) /\ getr regs 23 = w64 (c_n cx - Z.min i (c_n cx)) /\
    getr regs 10 = w64 (6 - i) /\ getr regs 11 = w64 1 /\ getr regs 12 = w64 (d_obj cx OOUR + i) /\
    p_frame cx dsh_our ps_C2 W3 mem3 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
    pb_our cx i W3 mem3).

Ltac pb_awr_ro :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac pb_awr_fr FB E516 Efa :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
    [ apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat FB);
      [ reflexivity
      | rewrite ?ew_ewset_other by lia; rewrite E516; unfold w64; apply unsigned_lit_small; lia
      | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
        right; right; right; eexists _, _; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
        rewrite Efa; change (fs_frame_bytes DFRAME_CLASS) with 4096; lia
      | ] ];
  apply awr_ok_nil.
Ltac pb_awr_fa FB AA SS E516 E60 Efa :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
    [ apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat FB);
      [ reflexivity
      | rewrite ?ew_ewset_other by lia; rewrite E516; unfold w64; apply unsigned_lit_small; lia
      | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
        right; right; right; eexists _, _; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
        rewrite Efa; change (fs_frame_bytes DFRAME_CLASS) with 4096; lia
      | ]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (AA - SS));
      [ reflexivity
      | rewrite ?ew_ewset_other by lia; rewrite E60; unfold w64; rewrite unsigned_lit_small by lia; lia
      | cbn; unfold MFRAME, LLVMF_STK in *; lia
      | cbn; unfold MFRAME, LLVMF_STK in *; lia
      | ] ];
  apply awr_ok_nil.
Ltac pb_win E516 E60 :=
  let a := fresh "a" in let Ha := fresh "Ha" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a Ha (r & Hin & Hr); cbv beta;
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      try (rewrite ?ew_ewset_other in Hr by lia; first [rewrite E516 in Hr | rewrite E60 in Hr];
           unfold w64 in Hr; rewrite unsigned_lit_small in Hr by lia);
      lia |]);
  destruct Hin.
Ltac pb_mem_upd Hmem Hpres E516 E60 :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict ?Hh ?m1) (mrestrict ?Hh ?m2), HG : mem_grows (mrestrict ?Hh ?m1) (mrestrict ?Hh ?m2),
    HF : frame_of ?Ex ?rs ?m1 ?m2 |- _ =>
    lazymatch type of Hmem with forall a, _ -> (?lo <= a < ?hi) -> _ =>
      let H2 := fresh "Hmem" in
      pose proof (pb_mem_step Ex rs Hh _ m1 m2 (fun a => lo <= a < hi) HFr ltac:(pb_win E516 E60) Hmem) as H2;
      cbv beta in H2;
      clear Hmem; rename H2 into Hmem end;
    let H3 := fresh "Hpres" in
    pose proof (pb_pres_step Hh m1 m2 _ HG Hpres) as H3;
    clear Hpres; rename H3 into Hpres; clear HF HFr HG
  end.
Ltac pb_srr :=
  match goal with |- sv_denot _ (sr_get ?s1 ?r1) = sv_denot _ (sr_get ?s2 ?r2) =>
    let v1 := eval vm_compute in (sr_get s1 r1) in let v2 := eval vm_compute in (sr_get s2 r2) in
    change (sr_get s1 r1) with v1; change (sr_get s2 r2) with v2 end;
  cbn [sv_denot]; rewrite ?ew_ewset_other by lia; reflexivity.
Ltac pb_rreg HS r :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx r HS);
    let v := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with v;
    cbn [sv_denot]; rewrite ?ew_ewset_other by lia end.
Ltac rewin_w HS n lo hi tac :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := idx_of_base rs n in let i := eval vm_compute in i in
  let r := eval vm_compute in (nth i rs got_regionP) in
  let HS3 := fresh "HS3" in
  pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r lo hi) HS ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow _ Ex _ r lo hi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(tac))) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end.
Ltac rewin HS n lo hi :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := idx_of_base rs n in let i := eval vm_compute in i in
  let r := eval vm_compute in (nth i rs got_regionP) in
  let HS3 := fresh "HS3" in
  pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r lo hi) HS ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_narrow _ Ex _ r lo hi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(cbn; lia) ltac:(cbn; lia))) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end.
Ltac ro_base HS n := rewin_w HS n 0 0 ltac:(intros o Ho; lia).
Ltac pb_chunk HS off e v Hden Hv H E516 :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let rs := eval vm_compute in (ss_mem ssx) in
    let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
    let r := eval vm_compute in (nth i rs got_regionP) in
    pose proof (pb_val_of_ss Ex ssx msx Hh i r off e v HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])) Hden Hv) as H;
    cbn [base_val YP09.r_base] in H; rewrite ?ew_ewset_other in H by lia; rewrite E516 in H; unfold w64 in H;
    rewrite unsigned_lit_small in H by lia end.
Ltac pb_obl E32 E552 ly3 S3 cx HJ Hin3 :=
  lazymatch goal with |- range_addressable (rd_of _ (mrestrict (w_H ?Wx) ?mx)) (U ?Ex (SOff 32 0)) (U ?Ex (SOff 552%nat ?c)) ?len =>
    rewrite (pb_U Ex 32 SHADOW_OFF 0 ltac:(rewrite ?ew_ewset_other by lia; exact E32) ltac:(unfold SHADOW_OFF; lia)
      ltac:(unfold SHADOW_OFF; lia));
    rewrite (pb_U Ex 552 _ c ltac:(rewrite ?ew_ewset_other by lia; exact E552) ltac:(lia) ltac:(lia));
    change (rd_of SEGS (mrestrict (w_H Wx) mx)) with (aview SEGS (w_H Wx) mx);
    apply (pb_addr ly3 S3 Wx mx _ (c_p cx) (c_n cx) _ _ (proj1 HJ) Hin3); lia
  end.
Ltac pb_rewin_our HS lo hi E516 Hpres :=
  rewin_w HS 516%nat lo hi ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho;
    cbn [YP09.r_base base_val ms_mem restrict];
    rewrite ?ew_ewset_other by lia; rewrite E516; unfold w64; rewrite unsigned_lit_small by lia;
    apply apresent_writable; apply Hpres; left; lia).
Ltac pb_rewin_a HS lo hi E60 Hpres :=
  rewin_w HS 60%nat lo hi ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho;
    cbn [YP09.r_base base_val ms_mem restrict];
    rewrite ?ew_ewset_other by lia; rewrite E60; unfold w64; rewrite unsigned_lit_small by lia;
    apply apresent_writable; apply Hpres; right; unfold MFRAME, LLVMF_STK in *; lia).
Ltac pb_br_ne E554 Hc c :=
  exfalso; lazymatch type of E554 with ew _ _ = w64 ?v =>
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    let E5 := fresh "E5" in
    assert (E5 : ew Ex 554 = w64 v) by (rewrite ?ew_ewset_other by lia; exact E554);
    first [ rewrite (proj1 (pb_branch Ex 554 v c E5 ltac:(lia) ltac:(lia))) in Hc
          | rewrite (proj2 (pb_branch Ex 554 v c E5 ltac:(lia) ltac:(lia))) in Hc ];
    first [ apply negb_false_iff, Z.eqb_eq in Hc | apply negb_true_iff, Z.eqb_neq in Hc
          | apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc ]; lia end end.
Ltac pb_ge_ref E552 :=
  exfalso; lazymatch type of E552 with ew _ _ = w64 ?v =>
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex ?a) (sv_denot _ (SLit 7)) = true |- _ =>
    let E5 := fresh "E5" in
    assert (E5 : ew Ex 552 = w64 v) by (rewrite ?ew_ewset_other by lia; exact E552);
    rewrite (denot_lit_U Ex a), (pb_and7 Ex 552 v 1 E5 ltac:(lia) ltac:(lia)) in Hc;
    change (sv_denot Ex (SLit 7)) with (Z_to_bv 64 7) in Hc;
    rewrite pb_ge_small in Hc by (pose proof (Z.mod_pos_bound (v + 1) 8 ltac:(lia)); lia);
    apply negb_true_iff, Z.ltb_ge in Hc; lia end end.
Ltac pb_rbase_ok HS W regs Hregs0 Hrb :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let RG := fresh "RG" in
  assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 27]%bv -> getr (ms_regs msx) r = getr regs r) by
    (let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
     rewrite (st_ok_pi_restrict_reg (w_H W) Ex ssx msx r HS), (Hregs0 r);
     cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [pb_srr|]); destruct Hr);
  let Hsp := fresh "Hsp" in let Hgp := fresh "Hgp" in let Htp := fresh "Htp" in let H8 := fresh "H8" in
  let H9 := fresh "H9" in let H19 := fresh "H19" in let H27 := fresh "H27" in
  destruct Hrb as (Hsp & Hgp & Htp & H8 & H9 & H19 & H27); unfold p_rbase, spZ in *;
  rewrite !RG by (cbn [In]; repeat (first [left; reflexivity | right])); repeat split; assumption end.
Ltac pb_land_pre HS cx E0 HE0 HFL0 fq ly3 S3 W k Hbase HJ Hfrs acs HF3 :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    let HdEx := fresh "HdEx" in let HFLx := fresh "HFLx" in
    assert (HdEx : d_E cx Ex) by (apply (d_E_agree cx E0);
      [let mm := fresh "mm" in let Hmm := fresh "Hmm" in intros mm Hmm;
       rewrite ?ew_ewset_other by (unfold AT_FL in *; lia); reflexivity | exact HE0]);
    assert (HFLx : ew Ex AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
      by (rewrite ?ew_ewset_other by (unfold AT_FL; lia); exact HFL0);
    destruct (p_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx dsh_our acs ly3 S3 W _ k Ex ssx msx
      (conj Hbase (conj HJ Hfrs)) HdEx HFLx HS ltac:(vm_compute; reflexivity)) as [HF3 _]
  end.
Ltac pb_land_d HS W fq ly3 S3 k acc Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc sel :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    let Hms := fresh "Hms" in
    pose proof (st_ok_pi_restrict_mkst (w_H W) Ex ssx msx HS eq_refl) as Hms; cbn [ss_pc] in Hms;
    apply SRr_ret; sel;
    exists fq, ly3, S3, (ms_regs msx), (ms_mem msx); eexists; exists k, acc;
    split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|];
    split; [exact Hfrm|]; split; [exact Hbase|]; split; [exact HJ|]; split; [exact Hfrs|]; split; [exact Hk|]; split; [exact Hnev|];
    split; [exact Hmo|]; split; [exact Hacc|]
  end.
Ltac pb_our_old HS W mem3 Hmem Hour :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem msx));
    [let kk := fresh "kk" in let Hkk := fresh "Hkk" in intros kk Hkk; apply Hmem; unfold d_obj, dobj_off in *; lia
    | apply Hour; lia] end.

Lemma pb_start : forall cx W c, pro_C2 B MT XM_LIB RLO RHI tfib_K cx W c -> pb_inv cx 0 W c.
Proof.
intros cx W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hcan & (Hrb & H22 & H24 & H21 & H23 & H10 & H11 & H12) & Hframe & Hab).
destruct (pb_base_in cx Hbase) as (Hlen & _ & _).
exists fq, ly3, S3, regs, mem3, md3, k, acc.
split; [exact Hc|]. split; [exact Hfrm|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hcan|]. split; [lia|]. split; [exact Hrb|]. split; [exact H22|]. split; [exact H24|].
split; [rewrite Z.min_l by lia; rewrite Z.add_0_r; exact H21|].
split; [rewrite Z.min_l by lia; rewrite Z.sub_0_r; exact H23|].
split; [exact H10|]. split; [exact H11|].
split; [rewrite Z.add_0_r; exact H12|].
split; [exact Hframe|]. split; [exact Hab|].
intros j Hj. lia.
Qed.

Lemma pb_inv_range : forall cx i W c, pb_inv cx i W c -> 0 <= i < 6.
Proof.
intros cx i W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _).
exact Hi.
Qed.

Lemma pb_copy : forall cx i W c, pb_inv cx i W c -> 0 <= i < 5 -> i < c_n cx ->
  SRr SEGS W c (pb_inv cx (i + 1)).
Proof.
intros cx i W c H Hi5 Hn.

destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hcan & Hi & Hrb & H22 & H24 & H21 & H23 & H10 & H11 & H12 & Hframe & Hab & Hour).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (HFr : 0 <= d_FB cx < 2 ^ 64) by lia.
assert (HFA : d_FB cx + 4096 <= d_A cx) by (unfold MFRAME, LLVMF_STK in *; lia).
destruct (pb_base_in cx Hbase) as (Hlen & Hin & _).
destruct Hframe as (E & HdE & Hregs & Hflag).
rewrite Z.min_l in H21, H23 by lia.
destruct (Hin ltac:(lia)) as (Hn26 & Hin0).
assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (rewrite Hab; exact Hin0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (Hp16 & Hp4096 & Hpc & _ & _ & _ & Hnmx).
assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
rewrite Hrq in Hpc.
assert (H12' : getr regs 12 = w64 (d_FB cx + (2128 + i))) by (rewrite H12; unfold d_obj, dobj_off; f_equal; lia).
pose proof (regs_ok_pb cx E regs (6 - i) (2128 + i) (pb_xs (c_pl cx) i 1 ++ []) HdE Hrb H22 H24 H10 H11 H12' HAr HFr) as Hregs0.
pose proof (pb_seat fq cx (6 - i) (2128 + i) i 1 [] W ly3 S3 regs mem3 md3 k E HctxD HdE Hregs Hflag Hregs0 H21 Hab
  ltac:(lia) ltac:(right; split; [left; reflexivity | cbn; lia])) as HS.
pose proof (d_E_env cx E (pb_vals regs (pb_xs (c_pl cx) i 1 ++ [])) HdE) as HE0.
pose proof (d_env_fl cx E (pb_vals regs (pb_xs (c_pl cx) i 1 ++ []))) as HFL0.
assert (E0_552 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) i 1 ++ []))) 552 = w64 (c_p cx + i))
  by (rewrite (pb_env_r cx E regs _ 21) by lia; exact H21).
assert (E0_554 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) i 1 ++ []))) 554 = w64 (c_n cx - i))
  by (rewrite (pb_env_r cx E regs _ 23) by lia; exact H23).
assert (E0_563 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) i 1 ++ []))) 563 = Z_to_bv 64 (rdb (c_pl cx) (Z.to_nat i + 0))).
{ pose proof (pb_env_x cx E regs (pb_xs (c_pl cx) i 1 ++ []) 0 ltac:(rewrite length_app, pb_xs_len; cbn; lia)) as X.
  change (AT_X + 32 + 0)%nat with 563%nat in X. rewrite X. rewrite app_nth1 by (rewrite pb_xs_len; lia).
  apply pb_xs_nth. lia. }
set (E0 := d_env cx E (pb_vals regs (pb_xs (c_pl cx) i 1 ++ []))) in *. clearbody E0.
pose proof HE0 as (_ & E0_32 & HEI & E0_60 & E0_516 & _). change AT_F with 516%nat in E0_516. change AT_A with 60%nat in E0_60.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E0 (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + POFF_C2)) with (Z_to_bv 64 (BASE + POFF_C2)).
assert (Hmem : forall a, 0 <= a < 2 ^ 64 -> d_FB cx + 2128 <= a < d_FB cx + 2128 + i ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a) by reflexivity.
assert (Hpres : forall a, (d_FB cx <= a < d_FB cx + 4096) \/ (d_S cx - LLVMF_STK <= a < d_S cx) -> apresent (w_H W) mem3 a)
  by (intros a [Ha | Ha]; [exact (HFpres a Ha) | exact (HWpres a Ha)]).
unfold ss_p in HS.
assert (Hil : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
destruct Hil as [-> | [-> | [-> | [-> | ->]]]].
all: ro_base HS 529%nat; ro_base HS 60%nat; ro_base HS 516%nat.
all: psrr_branch_tok RUN BR HS SHOK PBspan; [pb_br_ne E0_554 Hc 0 |].
all: paj_run_tok RUN HS HJ SHOK PBspan; [pb_obl E0_32 E0_552 ly3 S3 cx HJ Hin3 | pb_awr_ro |].
all: pb_mem_upd Hmem Hpres E0_516 E0_60.
all: lazymatch type of H21 with getr _ _ = w64 (_ + ?i) => pb_rewin_our HS (2128 + i) (2129 + i) E0_516 Hpres end.
all: paj_run_to_tok RUNTO HS HJ SHOK PBspan0 POFF_C2; [pb_awr_fr (d_FB cx) E0_516 Efa|].
all: pb_mem_upd Hmem Hpres E0_516 E0_60.
all: pb_land_pre HS cx E0 HE0 HFL0 fq ly3 S3 W k Hbase HJ Hfrs ps_C2 Hframe3.
all: lazymatch type of H21 with getr _ _ = w64 (_ + ?i) =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (Hden : sv_denot Ex (SOff 563 0) = Z_to_bv 64 (rdb (c_pl cx) (Z.to_nat i + 0)))
      by (cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E0_563, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
    pb_chunk HS (2128 + i) (SOff 563 0) (rdb (c_pl cx) (Z.to_nat i + 0)) Hden (pb_rdb_lt (c_pl cx) (Z.to_nat i + 0)) Hby E0_516
  end end.
all: pb_land_d HS W fq ly3 S3 k acc Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc ltac:(unfold pb_inv, d_at).
all: lazymatch type of H21 with getr _ _ = w64 (_ + ?i) =>
  split; [exact Hcan|]; split; [lia|]; split; [pb_rbase_ok HS W regs Hregs0 Hrb|];
  split; [pb_rreg HS (22%bv : bv 5); rewrite E0_516; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|];
  split; [pb_rreg HS (24%bv : bv 5); rewrite E0_516; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|];
  split; [pb_rreg HS (21%bv : bv 5); rewrite E0_552; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|];
  split; [pb_rreg HS (23%bv : bv 5); rewrite E0_554; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|];
  split; [pb_rreg HS (10%bv : bv 5); reflexivity|]; split; [pb_rreg HS (11%bv : bv 5); reflexivity|];
  split; [pb_rreg HS (12%bv : bv 5); rewrite E0_516; unfold w64, d_obj, dobj_off; rewrite unsigned_lit_small by lia; f_equal; lia|];
  split; [exact Hframe3|]; split; [exact Hab|];
  let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj;
  destruct (Z.eq_dec j i) as [->|Hjn];
  [ unfold d_obj, dobj_off; replace (d_FB cx + 2128 + i) with (d_FB cx + (2128 + i)) by lia; exact Hby
  | pb_our_old HS W mem3 Hmem Hour ] end.
Qed.

Lemma pb_zstep : forall cx i W c, pb_inv cx i W c -> 0 <= i < 5 -> c_n cx <= i ->
  SRr SEGS W c (pb_inv cx (i + 1)).
Proof.
intros cx i W c H Hi5 Hn.

destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hcan & Hi & Hrb & H22 & H24 & H21 & H23 & H10 & H11 & H12 & Hframe & Hab & Hour).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (HFr : 0 <= d_FB cx < 2 ^ 64) by lia.
assert (HFA : d_FB cx + 4096 <= d_A cx) by (unfold MFRAME, LLVMF_STK in *; lia).
destruct (pb_base_in cx Hbase) as (Hlen & Hin & _).
destruct Hframe as (E & HdE & Hregs & Hflag).
rewrite Z.min_r in H21, H23 by lia.
assert (Hpr : 0 <= c_p cx + c_n cx < 2 ^ 64).
{ destruct Hbase as ((_ & _ & _ & _ & Hpn & _) & _). destruct Hpn as [[Hz Hp] | [Hn0 Hin0]].
  - rewrite Hp, Hz. unfold A_EMPTY. lia.
  - assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (rewrite Hab; exact Hin0).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpc & _).
    unfold req_size in Hpc. destruct (Z.eqb_spec (c_n cx) 0); lia. }
assert (H12' : getr regs 12 = w64 (d_FB cx + (2128 + i))) by (rewrite H12; unfold d_obj, dobj_off; f_equal; lia).
pose proof (regs_ok_pb cx E regs (6 - i) (2128 + i) (pb_xs (c_pl cx) (c_n cx) 0 ++ []) HdE Hrb H22 H24 H10 H11 H12' HAr HFr) as Hregs0.
pose proof (pb_seat fq cx (6 - i) (2128 + i) (c_n cx) 0 [] W ly3 S3 regs mem3 md3 k E HctxD HdE Hregs Hflag Hregs0 H21 Hab
  ltac:(lia) (or_introl eq_refl)) as HS.
pose proof (d_E_env cx E (pb_vals regs (pb_xs (c_pl cx) (c_n cx) 0 ++ [])) HdE) as HE0.
pose proof (d_env_fl cx E (pb_vals regs (pb_xs (c_pl cx) (c_n cx) 0 ++ []))) as HFL0.
assert (E0_552 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) (c_n cx) 0 ++ []))) 552 = w64 (c_p cx + c_n cx))
  by (rewrite (pb_env_r cx E regs _ 21) by lia; exact H21).
assert (E0_554 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) (c_n cx) 0 ++ []))) 554 = w64 (c_n cx - c_n cx))
  by (rewrite (pb_env_r cx E regs _ 23) by lia; exact H23).
set (E0 := d_env cx E (pb_vals regs (pb_xs (c_pl cx) (c_n cx) 0 ++ []))) in *. clearbody E0.
pose proof HE0 as (_ & E0_32 & HEI & E0_60 & E0_516 & _). change AT_F with 516%nat in E0_516. change AT_A with 60%nat in E0_60.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E0 (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + POFF_C2)) with (Z_to_bv 64 (BASE + POFF_C2)).
assert (Hmem : forall a, 0 <= a < 2 ^ 64 -> d_FB cx + 2128 <= a < d_FB cx + 2128 + i ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a) by reflexivity.
assert (Hpres : forall a, (d_FB cx <= a < d_FB cx + 4096) \/ (d_S cx - LLVMF_STK <= a < d_S cx) -> apresent (w_H W) mem3 a)
  by (intros a [Ha | Ha]; [exact (HFpres a Ha) | exact (HWpres a Ha)]).
unfold ss_p in HS.
assert (Hil : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
destruct Hil as [-> | [-> | [-> | [-> | ->]]]].
all: ro_base HS 529%nat; ro_base HS 60%nat.
all: lazymatch type of H12' with getr _ _ = w64 (_ + (2128 + ?i)) => rewin HS 516%nat (2128 + i) (2129 + i) end.
all: psrr_branch_tok RUN BR HS SHOK PBspan0; [| pb_br_ne E0_554 Hc 0].
all: paj_run_to_tok RUNTO HS HJ SHOK PBspan0 0x534; [pb_awr_fr (d_FB cx) E0_516 Efa|].
all: pb_mem_upd Hmem Hpres E0_516 E0_60.
all: paj_run_to_tok RUNTO HS HJ SHOK PBspan0 POFF_C2; [pb_awr_fr (d_FB cx) E0_516 Efa|].
all: pb_mem_upd Hmem Hpres E0_516 E0_60.
all: pb_land_pre HS cx E0 HE0 HFL0 fq ly3 S3 W k Hbase HJ Hfrs ps_C2 Hframe3.
all: lazymatch type of H12' with getr _ _ = w64 (_ + (2128 + ?i)) =>
  pb_chunk HS (2128 + i) (SLit 0) 0 (@eq_refl word (Z_to_bv 64 0)) pb_byte0 Hby E0_516 end.
all: pb_land_d HS W fq ly3 S3 k acc Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc ltac:(unfold pb_inv, d_at).
all: lazymatch type of H12' with getr _ _ = w64 (_ + (2128 + ?i)) =>
  split; [exact Hcan|]; split; [lia|]; split; [pb_rbase_ok HS W regs Hregs0 Hrb|];
  split; [pb_rreg HS (22%bv : bv 5); rewrite E0_516; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|];
  split; [pb_rreg HS (24%bv : bv 5); rewrite E0_516; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|];
  split; [pb_rreg HS (21%bv : bv 5); rewrite E0_552; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|];
  split; [pb_rreg HS (23%bv : bv 5); rewrite E0_554; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|];
  split; [pb_rreg HS (10%bv : bv 5); reflexivity|]; split; [pb_rreg HS (11%bv : bv 5); reflexivity|];
  split; [pb_rreg HS (12%bv : bv 5); rewrite E0_516; unfold w64, d_obj, dobj_off; rewrite unsigned_lit_small by lia; f_equal; lia|];
  split; [exact Hframe3|]; split; [exact Hab|];
  let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj;
  destruct (Z.eq_dec j i) as [->|Hjn];
  [ rewrite pb_rdb_out by lia; unfold d_obj, dobj_off; replace (d_FB cx + 2128 + i) with (d_FB cx + (2128 + i)) by lia; exact Hby
  | pb_our_old HS W mem3 Hmem Hour ] end.
Qed.

Lemma pb_last_z : forall cx W c, pb_inv cx 5 W c -> c_n cx <= 5 ->
  SRr SEGS W c (pro_C3 B MT XM_LIB RLO RHI tfib_K cx).
Proof.
intros cx W c H Hn.

destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hcan & Hi & Hrb & H22 & H24 & H21 & H23 & H10 & H11 & H12 & Hframe & Hab & Hour).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (HFr : 0 <= d_FB cx < 2 ^ 64) by lia.
assert (HFA : d_FB cx + 4096 <= d_A cx) by (unfold MFRAME, LLVMF_STK in *; lia).
destruct (pb_base_in cx Hbase) as (Hlen & Hin & _).
destruct Hframe as (E & HdE & Hregs & Hflag).
rewrite Z.min_r in H21, H23 by lia.
assert (Hpr : 0 <= c_p cx + c_n cx < 2 ^ 64).
{ destruct Hbase as ((_ & _ & _ & _ & Hpn & _) & _). destruct Hpn as [[Hz Hp] | [Hn0 Hin0]].
  - rewrite Hp, Hz. unfold A_EMPTY. lia.
  - assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (rewrite Hab; exact Hin0).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpc & _).
    unfold req_size in Hpc. destruct (Z.eqb_spec (c_n cx) 0); lia. }
assert (H12' : getr regs 12 = w64 (d_FB cx + (2128 + 5))) by (rewrite H12; unfold d_obj, dobj_off; f_equal; lia).
pose proof (regs_ok_pb cx E regs (6 - 5) (2128 + 5) (pb_xs (c_pl cx) (c_n cx) 0 ++ []) HdE Hrb H22 H24 H10 H11 H12' HAr HFr) as Hregs0.
pose proof (pb_seat fq cx (6 - 5) (2128 + 5) (c_n cx) 0 [] W ly3 S3 regs mem3 md3 k E HctxD HdE Hregs Hflag Hregs0 H21 Hab
  ltac:(lia) (or_introl eq_refl)) as HS.
pose proof (d_E_env cx E (pb_vals regs (pb_xs (c_pl cx) (c_n cx) 0 ++ [])) HdE) as HE0.
pose proof (d_env_fl cx E (pb_vals regs (pb_xs (c_pl cx) (c_n cx) 0 ++ []))) as HFL0.
assert (E0_552 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) (c_n cx) 0 ++ []))) 552 = w64 (c_p cx + c_n cx))
  by (rewrite (pb_env_r cx E regs _ 21) by lia; exact H21).
assert (E0_554 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) (c_n cx) 0 ++ []))) 554 = w64 (c_n cx - c_n cx))
  by (rewrite (pb_env_r cx E regs _ 23) by lia; exact H23).
set (E0 := d_env cx E (pb_vals regs (pb_xs (c_pl cx) (c_n cx) 0 ++ []))) in *. clearbody E0.
pose proof HE0 as (_ & E0_32 & HEI & E0_60 & E0_516 & _). change AT_F with 516%nat in E0_516. change AT_A with 60%nat in E0_60.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E0 (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + POFF_C2)) with (Z_to_bv 64 (BASE + POFF_C2)).
assert (Hmem : forall a, 0 <= a < 2 ^ 64 -> d_FB cx + 2128 <= a < d_FB cx + 2128 + 5 ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a) by reflexivity.
assert (Hpres : forall a, (d_FB cx <= a < d_FB cx + 4096) \/ (d_S cx - LLVMF_STK <= a < d_S cx) -> apresent (w_H W) mem3 a)
  by (intros a [Ha | Ha]; [exact (HFpres a Ha) | exact (HWpres a Ha)]).
unfold ss_p in HS.
ro_base HS 529%nat. rewin HS 60%nat 32 48. rewin HS 516%nat 2133 2134.
psrr_branch_tok RUN BR HS SHOK PBspan0; [| pb_br_ne E0_554 Hc 0].
paj_run_to_tok RUNTO HS HJ SHOK PBspan0 POFF_C3; [pb_awr_fa (d_FB cx) (d_A cx) (d_S cx) E0_516 E0_60 Efa|].
pb_mem_upd Hmem Hpres E0_516 E0_60.
pb_land_pre HS cx E0 HE0 HFL0 fq ly3 S3 W k Hbase HJ Hfrs ps_C3 Hframe3.
pb_chunk HS (2128 + 5) (SLit 0) 0 (@eq_refl word (Z_to_bv 64 0)) pb_byte0 Hz E0_516.
pb_land_d HS W fq ly3 S3 k acc Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc ltac:(unfold pro_C3, d_at).
split; [exact Hcan|].
split; [split; [pb_rbase_ok HS W regs Hregs0 Hrb|];
  split; [pb_rreg HS (18%bv : bv 5); unfold p_setup; rewrite pb_rdb_out by lia; reflexivity|];
  split; [pb_rreg HS (24%bv : bv 5); rewrite E0_552; unfold w64, d_cur, p_n3; rewrite unsigned_lit_small by lia; f_equal; lia|];
  pb_rreg HS (23%bv : bv 5); rewrite E0_554; unfold w64, p_n3; rewrite unsigned_lit_small by lia; f_equal; lia|].
split; [exact Hframe3|]. split; [exact Hab|].
apply pb_garr8_our. intros j Hj. destruct (Z.eq_dec j 5) as [->|Hjn].
+ rewrite pb_rdb_out by lia. unfold d_obj, dobj_off. replace (d_FB cx + 2128 + 5) with (d_FB cx + (2128 + 5)) by lia. exact Hz.
+ pb_our_old HS W mem3 Hmem Hour.
Qed.

Lemma pb_last_6 : forall cx W c, pb_inv cx 5 W c -> c_n cx = 6 ->
  SRr SEGS W c (pro_C3 B MT XM_LIB RLO RHI tfib_K cx).
Proof.
intros cx W c H Hn.

destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hcan & Hi & Hrb & H22 & H24 & H21 & H23 & H10 & H11 & H12 & Hframe & Hab & Hour).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (HFr : 0 <= d_FB cx < 2 ^ 64) by lia.
assert (HFA : d_FB cx + 4096 <= d_A cx) by (unfold MFRAME, LLVMF_STK in *; lia).
destruct (pb_base_in cx Hbase) as (Hlen & Hin & _).
destruct Hframe as (E & HdE & Hregs & Hflag).
rewrite Z.min_l in H21, H23 by lia.
destruct (Hin ltac:(lia)) as (Hn26 & Hin0).
assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (rewrite Hab; exact Hin0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (Hp16 & Hp4096 & Hpc & _ & _ & _ & Hnmx).
assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
rewrite Hrq in Hpc.
assert (H12' : getr regs 12 = w64 (d_FB cx + (2128 + 5))) by (rewrite H12; unfold d_obj, dobj_off; f_equal; lia).
pose proof (regs_ok_pb cx E regs (6 - 5) (2128 + 5) (pb_xs (c_pl cx) 5 1 ++ []) HdE Hrb H22 H24 H10 H11 H12' HAr HFr) as Hregs0.
pose proof (pb_seat fq cx (6 - 5) (2128 + 5) 5 1 [] W ly3 S3 regs mem3 md3 k E HctxD HdE Hregs Hflag Hregs0 H21 Hab
  ltac:(lia) ltac:(right; split; [left; reflexivity | cbn; lia])) as HS.
pose proof (d_E_env cx E (pb_vals regs (pb_xs (c_pl cx) 5 1 ++ [])) HdE) as HE0.
pose proof (d_env_fl cx E (pb_vals regs (pb_xs (c_pl cx) 5 1 ++ []))) as HFL0.
assert (E0_552 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) 5 1 ++ []))) 552 = w64 (c_p cx + 5))
  by (rewrite (pb_env_r cx E regs _ 21) by lia; exact H21).
assert (E0_554 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) 5 1 ++ []))) 554 = w64 (c_n cx - 5))
  by (rewrite (pb_env_r cx E regs _ 23) by lia; exact H23).
assert (E0_563 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) 5 1 ++ []))) 563 = Z_to_bv 64 (rdb (c_pl cx) (Z.to_nat 5 + 0))).
{ pose proof (pb_env_x cx E regs (pb_xs (c_pl cx) 5 1 ++ []) 0 ltac:(rewrite length_app, pb_xs_len; cbn; lia)) as X.
  change (AT_X + 32 + 0)%nat with 563%nat in X. rewrite X. rewrite app_nth1 by (rewrite pb_xs_len; lia).
  apply pb_xs_nth. lia. }
set (E0 := d_env cx E (pb_vals regs (pb_xs (c_pl cx) 5 1 ++ []))) in *. clearbody E0.
pose proof HE0 as (_ & E0_32 & HEI & E0_60 & E0_516 & _). change AT_F with 516%nat in E0_516. change AT_A with 60%nat in E0_60.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E0 (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + POFF_C2)) with (Z_to_bv 64 (BASE + POFF_C2)).
assert (Hmem : forall a, 0 <= a < 2 ^ 64 -> d_FB cx + 2128 <= a < d_FB cx + 2128 + 5 ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a) by reflexivity.
assert (Hpres : forall a, (d_FB cx <= a < d_FB cx + 4096) \/ (d_S cx - LLVMF_STK <= a < d_S cx) -> apresent (w_H W) mem3 a)
  by (intros a [Ha | Ha]; [exact (HFpres a Ha) | exact (HWpres a Ha)]).
unfold ss_p in HS.
ro_base HS 529%nat. ro_base HS 60%nat. ro_base HS 516%nat.
psrr_branch_tok RUN BR HS SHOK PBspan; [pb_br_ne E0_554 Hc 0 |].
paj_run_tok RUN HS HJ SHOK PBspan; [pb_obl E0_32 E0_552 ly3 S3 cx HJ Hin3 | pb_awr_ro |].
pb_mem_upd Hmem Hpres E0_516 E0_60.
pb_rewin_our HS 2133 2134 E0_516 Hpres. pb_rewin_a HS 32 48 E0_60 Hpres.
paj_run_tok RUN HS HJ SHOK PBspan0; [pb_awr_fa (d_FB cx) (d_A cx) (d_S cx) E0_516 E0_60 Efa|].
pb_mem_upd Hmem Hpres E0_516 E0_60.
psrr_branch_tok RUN BR HS SHOK PBspan0; [| pb_br_ne E0_554 Hc0 (-1)].
paj_run_to_tok RUNTO HS HJ SHOK PBspan0 POFF_C3; [pb_awr_fa (d_FB cx) (d_A cx) (d_S cx) E0_516 E0_60 Efa|].
pb_mem_upd Hmem Hpres E0_516 E0_60.
pb_land_pre HS cx E0 HE0 HFL0 fq ly3 S3 W k Hbase HJ Hfrs ps_C3 Hframe3.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (Hden : sv_denot Ex (SOff 563 0) = Z_to_bv 64 (rdb (c_pl cx) (Z.to_nat 5 + 0)))
    by (cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E0_563, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  pb_chunk HS (2128 + 5) (SOff 563 0) (rdb (c_pl cx) (Z.to_nat 5 + 0)) Hden (pb_rdb_lt (c_pl cx) (Z.to_nat 5 + 0)) Hby E0_516
end.
pb_land_d HS W fq ly3 S3 k acc Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc ltac:(unfold pro_C3, d_at).
split; [exact Hcan|].
split; [split; [pb_rbase_ok HS W regs Hregs0 Hrb|];
  split; [pb_rreg HS (18%bv : bv 5); unfold p_setup; rewrite pb_rdb_out by lia; reflexivity|];
  split; [pb_rreg HS (24%bv : bv 5); rewrite E0_552; unfold w64, d_cur, p_n3; rewrite unsigned_lit_small by lia; f_equal; lia|];
  pb_rreg HS (23%bv : bv 5); rewrite E0_554; unfold w64, p_n3; rewrite unsigned_lit_small by lia; f_equal; lia|].
split; [exact Hframe3|]. split; [exact Hab|].
apply pb_garr8_our. intros j Hj. destruct (Z.eq_dec j 5) as [->|Hjn].
+ unfold d_obj, dobj_off. replace (d_FB cx + 2128 + 5) with (d_FB cx + (2128 + 5)) by lia. exact Hby.
+ pb_our_old HS W mem3 Hmem Hour.
Qed.

Lemma pb_last_7 : forall cx W c, pb_inv cx 5 W c -> 7 <= c_n cx ->
  SRr SEGS W c (pro_C3 B MT XM_LIB RLO RHI tfib_K cx).
Proof.
intros cx W c H Hn.

destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hcan & Hi & Hrb & H22 & H24 & H21 & H23 & H10 & H11 & H12 & Hframe & Hab & Hour).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (HFr : 0 <= d_FB cx < 2 ^ 64) by lia.
assert (HFA : d_FB cx + 4096 <= d_A cx) by (unfold MFRAME, LLVMF_STK in *; lia).
destruct (pb_base_in cx Hbase) as (Hlen & Hin & _).
destruct Hframe as (E & HdE & Hregs & Hflag).
rewrite Z.min_l in H21, H23 by lia.
destruct (Hin ltac:(lia)) as (Hn26 & Hin0).
assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (rewrite Hab; exact Hin0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (Hp16 & Hp4096 & Hpc & Hpapp & _ & _ & Hnmx).
assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
rewrite Hrq in Hpc, Hpapp.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hin3 Hfin) as Hsep.
rewrite Efa, Hrq in Hsep. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
pose proof (pa_obj_img 0 ltac:(vm_compute; lia)) as HO0. pose proof (pa_obj_img 12 ltac:(vm_compute; lia)) as HO12.
unfold IMG_LO, IMG_TOP in HO0, HO12.
set (q := dsh_cell_addr (c_p cx + 5 + 1)).
assert (Hq : 0 <= q < 2 ^ 64) by (unfold q; apply shaddr_range; lia).
assert (H12' : getr regs 12 = w64 (d_FB cx + (2128 + 5))) by (rewrite H12; unfold d_obj, dobj_off; f_equal; lia).
pose proof (regs_ok_pb cx E regs (6 - 5) (2128 + 5) (pb_xs (c_pl cx) 5 2 ++ [Z_to_bv 64 q]) HdE Hrb H22 H24 H10 H11 H12' HAr HFr) as Hregs0.
pose proof (pb_seat fq cx (6 - 5) (2128 + 5) 5 2 [Z_to_bv 64 q] W ly3 S3 regs mem3 md3 k E HctxD HdE Hregs Hflag Hregs0 H21 Hab
  ltac:(lia) ltac:(right; split; [right; reflexivity | cbn; lia])) as HS.
pose proof (d_E_env cx E (pb_vals regs (pb_xs (c_pl cx) 5 2 ++ [Z_to_bv 64 q])) HdE) as HE0.
pose proof (d_env_fl cx E (pb_vals regs (pb_xs (c_pl cx) 5 2 ++ [Z_to_bv 64 q]))) as HFL0.
assert (E0_552 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) 5 2 ++ [Z_to_bv 64 q]))) 552 = w64 (c_p cx + 5))
  by (rewrite (pb_env_r cx E regs _ 21) by lia; exact H21).
assert (E0_554 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) 5 2 ++ [Z_to_bv 64 q]))) 554 = w64 (c_n cx - 5))
  by (rewrite (pb_env_r cx E regs _ 23) by lia; exact H23).
assert (E0_563 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) 5 2 ++ [Z_to_bv 64 q]))) 563 = Z_to_bv 64 (rdb (c_pl cx) (Z.to_nat 5 + 0))).
{ pose proof (pb_env_x cx E regs (pb_xs (c_pl cx) 5 2 ++ [Z_to_bv 64 q]) 0 ltac:(rewrite length_app, pb_xs_len; cbn; lia)) as X.
  change (AT_X + 32 + 0)%nat with 563%nat in X. rewrite X. rewrite app_nth1 by (rewrite pb_xs_len; lia).
  apply pb_xs_nth. lia. }
assert (E0_564 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) 5 2 ++ [Z_to_bv 64 q]))) 564 = Z_to_bv 64 (rdb (c_pl cx) (Z.to_nat 5 + 1))).
{ pose proof (pb_env_x cx E regs (pb_xs (c_pl cx) 5 2 ++ [Z_to_bv 64 q]) 1 ltac:(rewrite length_app, pb_xs_len; cbn; lia)) as X.
  change (AT_X + 32 + 1)%nat with 564%nat in X. rewrite X. rewrite app_nth1 by (rewrite pb_xs_len; lia).
  apply pb_xs_nth. lia. }
assert (E0_565 : ew (d_env cx E (pb_vals regs (pb_xs (c_pl cx) 5 2 ++ [Z_to_bv 64 q]))) 565 = w64 q).
{ pose proof (pb_env_x cx E regs (pb_xs (c_pl cx) 5 2 ++ [Z_to_bv 64 q]) 2 ltac:(rewrite length_app, pb_xs_len; cbn; lia)) as X.
  change (AT_X + 32 + 2)%nat with 565%nat in X. rewrite X. rewrite app_nth2 by (rewrite pb_xs_len; lia).
  rewrite pb_xs_len. reflexivity. }
set (E0 := d_env cx E (pb_vals regs (pb_xs (c_pl cx) 5 2 ++ [Z_to_bv 64 q]))) in *. clearbody E0.
pose proof HE0 as (E0_EE & E0_32 & HEI & E0_60 & E0_516 & E0_529). change AT_F with 516%nat in E0_516. change AT_A with 60%nat in E0_60.
change AT_SH with 529%nat in E0_529.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E0 (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + POFF_C2)) with (Z_to_bv 64 (BASE + POFF_C2)).
assert (Hmem : forall a, 0 <= a < 2 ^ 64 -> d_FB cx + 2128 <= a < d_FB cx + 2128 + 5 ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a) by reflexivity.
assert (Hpres : forall a, (d_FB cx <= a < d_FB cx + 4096) \/ (d_S cx - LLVMF_STK <= a < d_S cx) -> apresent (w_H W) mem3 a)
  by (intros a [Ha | Ha]; [exact (HFpres a Ha) | exact (HWpres a Ha)]).
assert (U2 : bv_unsigned (ew E0 2) = d_S cx) by (rewrite (E0_EE 2%nat 2%bv eq_refl); reflexivity).
assert (U60 : bv_unsigned (ew E0 60) = d_A cx) by (rewrite E0_60; apply unsigned_lit_small; exact HAr).
assert (U516 : bv_unsigned (ew E0 516) = d_FB cx) by (rewrite E0_516; apply unsigned_lit_small; exact HFr).
assert (U529 : bv_unsigned (ew E0 529) = shadow_addr (d_FB cx))
  by (rewrite E0_529; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (U241 : bv_unsigned (ew E0 241) = VAL (A_OBJ 0)).
{ change 241%nat with (A_OBJ 0). rewrite (img_env_atomP E0 (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). apply unsigned_lit_small. apply pa_val_range. }
assert (U253 : bv_unsigned (ew E0 253) = VAL (A_OBJ 12)).
{ change 253%nat with (A_OBJ 12). rewrite (img_env_atomP E0 (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). apply unsigned_lit_small. apply pa_val_range. }
assert (U552 : bv_unsigned (ew E0 552) = c_p cx + 5) by (rewrite E0_552; unfold w64; apply unsigned_lit_small; lia).
assert (U565 : bv_unsigned (ew E0 565) = q) by (rewrite E0_565; unfold w64; apply unsigned_lit_small; exact Hq).
pose proof (dsh_cell_val B LAWS ly3 S3 W mem3 md3 (c_p cx) (c_n cx) (c_p cx + 5 + 1) (proj1 HJ) Hin3 ltac:(lia)) as Hcell.
fold q in Hcell.
unfold ss_p in HS.
destruct (Z.eq_dec (c_n cx) 7) as [H7 | H8].
1: assert (Hs : dsh_cell (c_p cx) (c_n cx) (c_p cx + 5 + 1) = 7)
     by (unfold dsh_cell; replace (c_p cx + 5 + 1 - c_p cx) with 6 by lia; rewrite H7; reflexivity).
2: assert (Hs : dsh_cell (c_p cx) (c_n cx) (c_p cx + 5 + 1) = 0)
     by (unfold dsh_cell; replace (c_p cx + 5 + 1 - c_p cx) with 6 by lia;
         destruct (Z.ltb_spec (6 / 8) (c_n cx / 8)) as [_ | Hge]; [reflexivity|];
         exfalso; assert (1 <= c_n cx / 8) by (apply Z.div_le_lower_bound; lia); change (6 / 8) with 0 in Hge; lia).
all: rewrite Hs in Hcell.
all: lazymatch type of Hs with _ = ?s =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    pose proof (st_ok_pi_add_region (L := lib_both3_0_listing) (PI := PI) Ex ssx msx (pb_cell_region 565 s) HS eq_refl
      (pb_cell_region_ok Ex W mem3 565 q s E0_565 Hq ltac:(lia) Hcell)
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint, pb_cell_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite U2, U60, U516, U529, U241, U253, U552, U565;
      unfold q, dsh_cell_addr, shadow_addr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, MFRAME, LLVMF_STK,
        IMG_LO, IMG_TOP, off_img in *;
      repeat split; lia)) as HS2
  end end.
all: clear HS; rename HS2 into HS; norm_ss HS.
all: ro_base HS 529%nat; ro_base HS 60%nat; ro_base HS 516%nat.
all: psrr_branch_tok RUN BR HS SHOK PBspan; [pb_br_ne E0_554 Hc 0 |].
all: paj_run_tok RUN HS HJ SHOK PBspan; [pb_obl E0_32 E0_552 ly3 S3 cx HJ Hin3 | pb_awr_ro |].
all: pb_mem_upd Hmem Hpres E0_516 E0_60.
all: pb_rewin_our HS 2133 2134 E0_516 Hpres; pb_rewin_a HS 32 48 E0_60 Hpres.
all: paj_run_tok RUN HS HJ SHOK PBspan0; [pb_awr_fa (d_FB cx) (d_A cx) (d_S cx) E0_516 E0_60 Efa|].
all: pb_mem_upd Hmem Hpres E0_516 E0_60.
all: psrr_branch_tok RUN BR HS SHOK PBspan0; [pb_br_ne E0_554 Hc0 (-1) |].
all: ro_base HS 516%nat; ro_base HS 60%nat.
all: paj_run_to_tok RUNTO HS HJ SHOK PBspan0 0x57c; [pb_awr_ro|].
all: pb_mem_upd Hmem Hpres E0_516 E0_60.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let E552x := fresh "E552x" in let E32x := fresh "E32x" in let E565x := fresh "E565x" in let Hden0 := fresh "Hden0" in
  assert (E552x : ew Ex 552 = w64 (c_p cx + 5)) by (rewrite ?ew_ewset_other by lia; exact E0_552);
  assert (E32x : ew Ex 32 = w64 SHADOW_OFF) by (rewrite ?ew_ewset_other by lia; exact E0_32);
  assert (E565x : ew Ex 565 = w64 q) by (rewrite ?ew_ewset_other by lia; exact E0_565);
  assert (Hden0 : sv_denot Ex (SOff 565 0) = getr (ms_regs msx) 10%bv) by
    (rewrite (st_ok_pi_restrict_reg (w_H W) Ex ssx msx 10%bv HS);
     let v := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in change (sr_get (ss_regs ssx) 10%bv) with v;
     symmetry; exact (dsh_cell_denot Ex 552 565 1 (c_p cx + 5) E552x ltac:(lia) ltac:(lia) ltac:(lia) E32x E565x));
  pose proof (ast_ok_pi_set_reg_fp (PI := PI) Ex ssx (restrict (w_H W) msx) 10%bv (SOff 565 0) HS eq_refl Hden0) as HS2
end.
all: clear HS; rename HS2 into HS; norm_ss HS.
1: paj_run_tok RUN HS HJ SHOK PBspan0; [pb_awr_ro|].
1: pb_mem_upd Hmem Hpres E0_516 E0_60.
1: psrr_branch_tok RUN BR HS SHOK PBspan0; [pb_ge_ref E0_552 |].
all: paj_run_to_tok RUNTO HS HJ SHOK PBspan0 POFF_C3; [pb_awr_ro|].
all: pb_mem_upd Hmem Hpres E0_516 E0_60.
all: pb_land_pre HS cx E0 HE0 HFL0 fq ly3 S3 W k Hbase HJ Hfrs ps_C3 Hframe3.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (Hden : sv_denot Ex (SOff 563 0) = Z_to_bv 64 (rdb (c_pl cx) (Z.to_nat 5 + 0)))
    by (cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E0_563, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  pb_chunk HS (2128 + 5) (SOff 563 0) (rdb (c_pl cx) (Z.to_nat 5 + 0)) Hden (pb_rdb_lt (c_pl cx) (Z.to_nat 5 + 0)) Hby E0_516
end.
all: pb_land_d HS W fq ly3 S3 k acc Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc ltac:(unfold pro_C3, d_at).
all: split; [exact Hcan|].
all: split; [split; [pb_rbase_ok HS W regs Hregs0 Hrb|];
  split; [pb_rreg HS (18%bv : bv 5); rewrite E0_564; unfold w64, p_setup; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
  split; [pb_rreg HS (24%bv : bv 5); rewrite E0_552; unfold w64, d_cur, p_n3; rewrite unsigned_lit_small by lia; f_equal; lia|];
  pb_rreg HS (23%bv : bv 5); rewrite E0_554; unfold w64, p_n3; rewrite unsigned_lit_small by lia; f_equal; lia|].
all: split; [exact Hframe3|]; split; [exact Hab|].
all: apply pb_garr8_our; intros j Hj; destruct (Z.eq_dec j 5) as [->|Hjn];
  [ unfold d_obj, dobj_off; replace (d_FB cx + 2128 + 5) with (d_FB cx + (2128 + 5)) by lia; exact Hby
  | pb_our_old HS W mem3 Hmem Hour ].
Qed.

Lemma pb_step : forall cx i W c, pb_inv cx i W c ->
  SRr SEGS W c (fun W' c' => pb_inv cx (i + 1) W' c' \/ pro_C3 B MT XM_LIB RLO RHI tfib_K cx W' c').
Proof.
intros cx i W c H.
pose proof (pb_inv_range cx i W c H) as Hi.
destruct (Z_lt_le_dec i 5) as [Hl | Hl].
- destruct (Z_lt_le_dec i (c_n cx)) as [Hc | Hc].
  + eapply SRr_mono; [exact (pb_copy cx i W c H ltac:(lia) Hc)|]. intros W' c' _ HI. left. exact HI.
  + eapply SRr_mono; [exact (pb_zstep cx i W c H ltac:(lia) Hc)|]. intros W' c' _ HI. left. exact HI.
- assert (i = 5) as -> by lia.
  destruct (Z_le_gt_dec (c_n cx) 5) as [H5 | H5].
  + eapply SRr_mono; [exact (pb_last_z cx W c H H5)|]. intros W' c' _ HC3. right. exact HC3.
  + destruct (Z.eq_dec (c_n cx) 6) as [H6 | H6].
    * eapply SRr_mono; [exact (pb_last_6 cx W c H H6)|]. intros W' c' _ HC3. right. exact HC3.
    * eapply SRr_mono; [exact (pb_last_7 cx W c H ltac:(lia))|]. intros W' c' _ HC3. right. exact HC3.
Qed.

Lemma pb_loop : forall (m : nat) cx i W c, (Z.to_nat (6 - i) <= m)%nat -> pb_inv cx i W c ->
  SRr SEGS W c (pro_C3 B MT XM_LIB RLO RHI tfib_K cx).
Proof.
induction m as [|m IH]; intros cx i W c Hm H.
- pose proof (pb_inv_range cx i W c H) as Hi. lia.
- eapply SRr_bind; [exact (pb_step cx i W c H)|].
  intros W' c' _ [Hinv | HC3].
  + pose proof (pb_inv_range cx (i + 1) W' c' Hinv) as Hi.
    exact (IH cx (i + 1) W' c' ltac:(lia) Hinv).
  + apply SRr_ret. exact HC3.
Qed.

Theorem pb_proB : pro_segB B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx W c H. exact (pb_loop 6 cx 0 W c ltac:(cbn; lia) (pb_start cx W c H)).
Qed.

End h.

End f.
End d.
