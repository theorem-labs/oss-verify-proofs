(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 628 of its 665 lines of code are new or changed and 32 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3u.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_observe_c reac_disco_table_observe.
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDOC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma nth_error_sub : forall (L : list byte) k n i, 0 <= k -> (i < n)%nat ->
  nth_error (DTC.sub L k n) i = nth_error L (Z.to_nat k + i).
Proof.
intros L k n i Hk Hi. unfold DTC.sub. rewrite nth_error_firstn.
destruct (Nat.ltb_spec i n) as [_|]; [|lia]. rewrite nth_error_skipn. reflexivity.
Qed.
Lemma length_sub_le : forall (L : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length L) ->
  length (DTC.sub L k n) = n.
Proof. intros L k n Hk H. unfold DTC.sub. rewrite length_firstn, length_skipn. lia. Qed.
Definition TS : list (Z * Z) :=
  [(88, 1); (80, 8); (72, 9); (64, 18); (56, 19); (48, 20); (40, 21); (32, 22); (24, 23); (16, 24); (8, 25); (0, 26)].
Definition tobs_stk_chunks : list YP09.chunk := Eval vm_compute in
  map (fun j => YP09.mkChunk (fst (nth j TS (0, 0))) (CVal 8 (SOff (32 + j) 0))) (seq 0 12).
Definition R_stk : YP09.region := YP09.mkRegion (Some 2%nat) 0 96 0 0 tobs_stk_chunks.
Definition R_hdr : YP09.region := YP09.mkRegion (Some 8%nat) 384 400 384 400 [YP09.mkChunk 384 (CData 0 384 16)].
Definition R_ent : YP09.region := YP09.mkRegion (Some 19%nat) 0 48 0 48 [YP09.mkChunk 0 (CData 2 0 48)].
Definition R_sig (so : Z) : YP09.region := YP09.mkRegion (Some 18%nat) so (so + 24) 0 0 [YP09.mkChunk so (CData 1 0 24)].
Definition tobs_regions (ent : bool) (so : Z) : smem :=
  R_stk :: R_hdr :: (if ent then [R_ent] else []) ++ [R_sig so].
Definition tobs_facts (ent : bool) (so : Z) : facts :=
  mkFacts ([ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 8 (2 ^ 47 - 401) 3); (22%nat, mkAF SB SB 0);
             (18%nat, if so =? 0 then mkAF 8 (2 ^ 47 - 25) 3 else mkAF 28 (2 ^ 47 - 5) 2) ] ++
           (if ent then [(19%nat, mkAF 8 (2 ^ 47 - 49) 3)] else [])) [] [].
Definition tobs_sr : list sv := Eval vm_compute in
  sr_set (sr_set sr_atoms 21%bv (SOff 8 384)) 24%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 384) (SLit 3)) (SOff 22 0)).
Definition tobs_ss (pc : Z) (ent : bool) (so : Z) : sstate := mkSS pc tobs_sr (tobs_regions ent so) None (tobs_facts ent so).
Definition TBx : sv := SOff 22 0.
Definition TBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition tobs_SH (ent : bool) (so : Z) : list shent :=
  mkSHE 8 0 400 :: (if ent then [mkSHE 19 0 48] else []) ++ [mkSHE 18 so (so + 24)].
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma garr8_mbyte : forall m p (L : list byte) j, garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L) ->
  (j < length L)%nat -> mbyte SEGS m (p + Z.of_nat j) = Some (nth j L (Z_to_bv 8 0)).
Proof.
intros m p L j HG Hj. destruct (HG j ltac:(rewrite length_map; exact Hj)) as [Hv Hr].
pose proof (Hv 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0. rewrite H0.
rewrite (nth_indep _ _ (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
rewrite map_nth. rewrite le_byte_1_0 by (pose proof (bv_unsigned_in_range 8 (nth j L (Z_to_bv 8 0))) as R; exact R).
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma chunk_cdata_garr8_s : forall E m p (L : list byte) d s len base off,
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L) -> ed E d = L ->
  0 <= s -> 0 <= len -> s + len <= Z.of_nat (length L) -> base + off = p + s ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CData d s len)).
Proof.
intros E m p L d s len base off HG Hd Hs Hl Hsl Hb. apply chunk_ok_cdata_intro; [exact Hs|].
intros i Hi. exists (nth (Z.to_nat (s + i)) L (Z_to_bv 8 0)). rewrite Hd. split.
- apply nth_error_nth'. lia.
- replace (base + off + i) with (p + Z.of_nat (Z.to_nat (s + i))) by lia. apply garr8_mbyte; [exact HG | lia].
Qed.
Lemma chunk_cdata_garr8_sub : forall E m p (L : list byte) d k len base off,
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L) -> ed E d = DTC.sub L k (Z.to_nat len) ->
  0 <= k -> 0 <= len -> k + len <= Z.of_nat (length L) -> base + off = p + k ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CData d 0 len)).
Proof.
intros E m p L d k len base off HG Hd Hk Hl Hkl Hb. apply chunk_ok_cdata_intro; [lia|].
intros i Hi. exists (nth (Z.to_nat (k + i)) L (Z_to_bv 8 0)). rewrite Hd. split.
- rewrite nth_error_sub by lia. replace (Z.to_nat k + Z.to_nat (0 + i))%nat with (Z.to_nat (k + i)) by lia.
  apply nth_error_nth'. lia.
- replace (base + off + i) with (p + Z.of_nat (Z.to_nat (k + i))) by lia. apply garr8_mbyte; [exact HG | lia].
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Record tctx : Type := mkTC {
  tSTK : Z; tsp0 : Z; tFP : list (Z * Z); tly : alayout; tS : astate; tW0 : world SEGS;
  tmem0 : word -> option byte; tmd0 : Model; town : list (Z * Z);
  tlyc : alayout; tSc : astate; tW : world SEGS; tmemc : word -> option byte; tmdc : Model; tk : Z;
  tregs : bvmap 5 word; tt : Z; ts : Z; tow : Z; tnow : Z; tT : list byte; tG : list byte }.
Record tpre (c : tctx) : Prop := mkTP {
  tp_J : ajournal SEGS B (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c) (tW0 c) (tmem0 c) (tmd0 c) (town c)
    (tlyc c) (tSc c) (tW c) (tmemc c) (tmdc c) (tk c);
  tp_rod : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (tW c)) (tmemc c));
  tp_ra : YK0s.ret_ok (YK11.getr (tregs c) 1);
  tp_ra4 : 4096 <= raZ (tregs c);
  tp_gp : YK11.getr (tregs c) 3 = w64 (as_gp B);
  tp_tp : YK11.getr (tregs c) 4 = w64 (as_tp B);
  tp_a0 : YK11.getr (tregs c) 10 = w64 (tt c);
  tp_a1 : YK11.getr (tregs c) 11 = w64 (ts c);
  tp_a2 : YK11.getr (tregs c) 12 = w64 (tow c);
  tp_a3 : YK11.getr (tregs c) 13 = w64 (tnow c);
  tp_ow : -2 ^ 31 <= tow c < 2 ^ 31;
  tp_now : 0 <= tnow c < 2 ^ 64;
  tp_al : spZ (tregs c) mod 16 = 0;
  tp_wlo : tsp0 c - tSTK c <= spZ (tregs c) - REAC_DISCO_TABLE_OBSERVE_STK;
  tp_whi : spZ (tregs c) <= tsp0 c;
  tp_t0 : 0 < tt c;
  tp_t8 : tt c mod 8 = 0;
  tp_t63 : tt c + 400 <= 2 ^ 63;
  tp_tam : amem_range (tt c) 400;
  tp_twin : spZ (tregs c) <= tt c \/ tt c + 400 <= spZ (tregs c) - REAC_DISCO_TABLE_OBSERVE_STK;
  tp_tawr : forall a, tt c <= a < tt c + 400 ->
     awr_byte (tSTK c) (tsp0 c) (tFP c) (ablocks B (tly c) (tS c)) (ablocks B (tlyc c) (tSc c)) (tlyc c) (town c) a /\
     apresent (w_H (tW c)) (tmemc c) a;
  tp_tra : range_addressable (aview SEGS (w_H (tW c)) (tmemc c)) SHADOW_OFF (tt c) 400;
  tp_thull : shadow_hull_vis (aview SEGS (w_H (tW c)) (tmemc c)) (tt c) 400;
  tp_T : garr8 SEGS (mrestrict (w_H (tW c)) (tmemc c)) (tt c) (map (fun b : byte => bv_unsigned b) (tT c));
  tp_Tl : length (tT c) = 400%nat;
  tp_s0 : 0 < ts c;
  tp_s63 : ts c + 24 <= 2 ^ 63;
  tp_sam : amem_range (ts c) 24;
  tp_s8 : ts c mod 8 = 0;
  tp_spres : forall a, ts c <= a < ts c + 24 -> apresent (w_H (tW c)) (tmemc c) a;
  tp_sra : range_addressable (aview SEGS (w_H (tW c)) (tmemc c)) SHADOW_OFF (ts c) 24;
  tp_swin : spZ (tregs c) <= ts c \/ ts c + 24 <= spZ (tregs c) - REAC_DISCO_TABLE_OBSERVE_STK;
  tp_shull : shadow_hull_vis (aview SEGS (w_H (tW c)) (tmemc c)) (ts c) 24;
  tp_G : garr8 SEGS (mrestrict (w_H (tW c)) (tmemc c)) (ts c) (map (fun b : byte => bv_unsigned b) (tG c));
  tp_Gl : length (tG c) = 24%nat;
  tp_st : ts c + 24 <= tt c \/ tt c + 400 <= ts c;
  tp_T1 : DTC.tbl_T1 (tT c);
  tp_T2 : DTC.tbl_T2 (tT c);
  tp_T3 : DTC.tbl_T3 (tT c);
  tp_S1 : DTC.sighting_S1 (tG c);
  tp_S2 : DTC.sighting_S2 (tG c) }.
Definition tpost (c : tctx) : world SEGS -> config -> Prop :=
  treac_disco_table_observe_post B fx (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c) (tW0 c) (tmem0 c) (tmd0 c) (town c)
    (tlyc c) (tSc c) (tW c) (tmemc c) (tk c) (tregs c) (tt c) (ts c) (tow c) (tnow c) (tT c) (tG c).
Definition tobs_frame (c : tctx) (m : word -> option byte) (sp1 : Z) : Prop :=
  Forall (fun p => val_mem SEGS m (sp1 + fst p) 8 (bv_unsigned (YK11.getr (tregs c) (Z_to_bv 5 (snd p))))) TS.
Definition tobs_kept (c : tctx) (m : word -> option byte) : Prop :=
  treac_disco_table_observe_kept B (tlyc c) (tSc c) (tW c) (tmemc c) (tW c) m (spZ (tregs c)) (tt c).
Record tobs_m (c : tctx) (regs1 : bvmap 5 word) (m1 : word -> option byte) (md1 : Model) (Tc : list byte) : Prop := mkTM {
  tm_J : ajournal SEGS B (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c) (tW0 c) (tmem0 c) (tmd0 c) (town c)
    (tlyc c) (tSc c) (tW c) m1 md1 (tk c);
  tm_sp : spZ regs1 = spZ (tregs c) - 96;
  tm_gp : YK11.getr regs1 3 = YK11.getr (tregs c) 3;
  tm_tp : YK11.getr regs1 4 = YK11.getr (tregs c) 4;
  tm_s11 : YK11.getr regs1 27 = YK11.getr (tregs c) 27;
  tm_s0 : YK11.getr regs1 8 = w64 (tt c);
  tm_s1 : YK11.getr regs1 9 = w64 (tow c);
  tm_s4 : YK11.getr regs1 20 = w64 (tnow c);
  tm_s5 : YK11.getr regs1 21 = w64 (tt c + 384);
  tm_s6 : YK11.getr regs1 22 = w64 SB;
  tm_s8 : YK11.getr regs1 24 = w64 (SB + (tt c + 384) / 8);
  tm_frame : tobs_frame c (mrestrict (w_H (tW c)) m1) (spZ regs1);
  tm_T : garr8 SEGS (mrestrict (w_H (tW c)) m1) (tt c) (map (fun b : byte => bv_unsigned b) Tc);
  tm_Tl : length Tc = 400%nat;
  tm_G : garr8 SEGS (mrestrict (w_H (tW c)) m1) (ts c) (map (fun b : byte => bv_unsigned b) (tG c));
  tm_tra : range_addressable (aview SEGS (w_H (tW c)) m1) SHADOW_OFF (tt c) 400;
  tm_sra : range_addressable (aview SEGS (w_H (tW c)) m1) SHADOW_OFF (ts c) 24;
  tm_thull : shadow_hull_vis (aview SEGS (w_H (tW c)) m1) (tt c) 400;
  tm_shull : shadow_hull_vis (aview SEGS (w_H (tW c)) m1) (ts c) 24;
  tm_tpres : forall a, tt c <= a < tt c + 400 -> apresent (w_H (tW c)) m1 a;
  tm_spres : forall a, ts c <= a < ts c + 24 -> apresent (w_H (tW c)) m1 a;
  tm_kept : tobs_kept c m1 }.
Definition tobs_extra (c : tctx) : list word := map (fun p => YK11.getr (tregs c) (Z_to_bv 5 (snd p))) TS.
Definition tobs_data (c : tctx) (Tc : list byte) (r : Z) (d : nat) : list byte :=
  match d with 0%nat => Tc | 1%nat => tG c | 2%nat => DTC.sub Tc (48 * r) 48 | _ => [] end.
Definition tobs_env (c : tctx) (regs1 : bvmap 5 word) (Tc : list byte) (r : Z) : env :=
  Eimg (mkEnv (ew (Ereg regs1 (tobs_extra c))) (tobs_data c Tc r)).
Lemma tobs_env_img : forall c regs1 Tc r, img_env VAL A_LIM (tobs_env c regs1 Tc r).
Proof. intros. unfold tobs_env. apply Eimg_env. Qed.
Lemma tobs_env_reg : forall c regs1 Tc r n (x : bv 5), Z.of_nat n = bv_unsigned x ->
  ew (tobs_env c regs1 Tc r) n = YK11.getr regs1 x.
Proof.
intros c regs1 Tc r n x Hn. unfold tobs_env. pose proof (u5_range x) as Hx.
rewrite Eimg_low by (unfold A_TEXT; lia). cbn [ew]. exact (ew_Ereg_nat regs1 _ n x Hn).
Qed.
Lemma tobs_env_extra : forall c regs1 Tc r j, (j < 12)%nat ->
  ew (tobs_env c regs1 Tc r) (32 + j) = YK11.getr (tregs c) (Z_to_bv 5 (snd (nth j TS (0, 0)))).
Proof.
intros c regs1 Tc r j Hj. unfold tobs_env. rewrite Eimg_low by (unfold A_TEXT; lia). cbn [ew].
rewrite ew_Ereg_extra. unfold tobs_extra.
do 12 (destruct j as [|j]; [reflexivity|]). lia.
Qed.
Lemma tobs_env_ed : forall c regs1 Tc r d, ed (tobs_env c regs1 Tc r) d = tobs_data c Tc r d.
Proof. reflexivity. Qed.
Lemma tobs_regs_ok : forall c regs1 Tc r,
  YK11.getr regs1 8 = w64 (tt c) -> YK11.getr regs1 21 = w64 (tt c + 384) -> YK11.getr regs1 22 = w64 SB ->
  YK11.getr regs1 24 = w64 (SB + (tt c + 384) / 8) -> 0 <= tt c -> tt c + 384 < 2 ^ 63 ->
  regs_ok (tobs_env c regs1 Tc r) tobs_sr regs1.
Proof.
intros c regs1 Tc r H8 H21 H22 H24 Ht0 Ht1.
assert (E8 : ew (tobs_env c regs1 Tc r) 8 = Z_to_bv 64 (tt c)) by (rewrite (tobs_env_reg c regs1 Tc r 8 8%bv eq_refl); exact H8).
assert (E22 : ew (tobs_env c regs1 Tc r) 22 = Z_to_bv 64 SB) by (rewrite (tobs_env_reg c regs1 Tc r 22 22%bv eq_refl); exact H22).
apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
repeat (destruct Hz as [<-|Hz];
  [ lazymatch goal with |- _ = sv_denot ?E (sr_get ?sr ?q) =>
      let v := eval vm_compute in (sr_get sr q) in change (sr_get sr q) with v end;
    first
    [ reflexivity
    | lazymatch goal with |- YK11.getr _ ?q = sv_denot _ (SOff ?n 0) =>
        cbn [sv_denot]; rewrite (tobs_env_reg c regs1 Tc r n q eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end
    | lazymatch goal with |- YK11.getr _ ?q = sv_denot _ (SOff 8 384) =>
        cbn [sv_denot]; rewrite E8, unsigned_lit_small by lia; exact H21 end
    | rewrite H24; rewrite (denot_shx _ 8 22 384 (tt c) SB E8 E22) by (unfold SB; lia); f_equal; lia ]
  | ]).
destruct Hz.
Qed.
Lemma tobs_stk_ok : forall c regs1 Tc r m sp1, tobs_frame c m sp1 ->
  Forall (YP09.chunk_ok SEGS (tobs_env c regs1 Tc r) m sp1) tobs_stk_chunks.
Proof.
intros c regs1 Tc r m sp1 Hf. unfold tobs_frame in Hf. rewrite Forall_forall in Hf.
apply Forall_forall. intros ch Hin. unfold tobs_stk_chunks in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<-|Hin];
  [ lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?a 0))) =>
      let j := eval cbv in (a - 32)%nat in
      let w := constr:(YK11.getr (tregs c) (Z_to_bv 5 (snd (nth j TS (0, 0))))) in
      apply (chunk_ok_val SEGS _ m sp1 o 8 (SOff a 0) (bv_unsigned w));
      [ cbn [sv_denot]; change a with (32 + j)%nat; rewrite (tobs_env_extra c regs1 Tc r j) by lia;
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (bv_unsigned_in_range 64 w) as Hr; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hr; exact Hr
      | cbn; lia
      | exact (Hf (o, snd (nth j TS (0, 0))) ltac:(cbn; tauto)) ] end
  | ]).
destruct Hin.
Qed.
Lemma tobs_app_apart : forall p n lo hi, amem_range p n -> 0 <= lo -> lo <= hi -> hi <= n ->
  forall x, p + Z.min lo hi <= x < p + Z.max lo hi -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof.
intros p n lo hi Ham Hlo Hlh Hhi x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.
Lemma tobs_enter : forall c regs1 m1 md1 Tc pc ent r so,
  tpre c -> tobs_m c regs1 m1 md1 Tc ->
  (so = 0 \/ so = -20) -> YK11.getr regs1 18 = w64 (ts c - so) ->
  (ent = true -> 0 <= r < 8 /\ YK11.getr regs1 19 = w64 (tt c + 48 * r)) ->
  st_ok_pi SEGS VAL (tobs_env c regs1 Tc r) (tobs_ss pc ent so)
    (restrict (w_H (tW c)) (YK11.mkst regs1 (Z_to_bv 64 (BASE + pc)) m1 (YK11.seg_rom SEGS))) /\
  sh_ok SEGS TBx (tobs_SH ent so) (tobs_env c regs1 Tc r) (mrestrict (w_H (tW c)) m1).
Proof.
intros c regs1 m1 md1 Tc pc ent r so HP HM Hso H18 Hent.
pose proof (tm_J _ _ _ _ _ HM) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (tp_wlo _ HP) as Hwlo. pose proof (tp_whi _ HP) as Hwhi. pose proof (tp_al _ HP) as Hal.
pose proof (tp_t0 _ HP) as Ht0. pose proof (tp_t8 _ HP) as Ht8. pose proof (tp_tam _ HP) as Htam. pose proof (tp_twin _ HP) as Htwin.
pose proof (tp_s0 _ HP) as Hs0. pose proof (tp_s8 _ HP) as Hs8. pose proof (tp_sam _ HP) as Hsam. pose proof (tp_swin _ HP) as Hswin.
pose proof (tp_st _ HP) as Hst. pose proof (tp_Gl _ HP) as HGl.
pose proof (tm_sp _ _ _ _ _ HM) as Hsp. pose proof (tm_Tl _ _ _ _ _ HM) as HTl.
pose proof (tm_T _ _ _ _ _ HM) as HT. pose proof (tm_G _ _ _ _ _ HM) as HG.
pose proof (tm_tra _ _ _ _ _ HM) as Htra. pose proof (tm_sra _ _ _ _ _ HM) as Hsra.
pose proof (tm_tpres _ _ _ _ _ HM) as Htpres.
assert (STK : REAC_DISCO_TABLE_OBSERVE_STK = 8288) by reflexivity. rewrite STK in Hwlo, Htwin, Hswin.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam, Hsam.
set (E := tobs_env c regs1 Tc r).
assert (E2 : bv_unsigned (ew E 2) = spZ (tregs c) - 96) by (subst E; rewrite (tobs_env_reg c regs1 Tc r 2 2%bv eq_refl); exact Hsp).
assert (E8 : ew E 8 = Z_to_bv 64 (tt c)) by (subst E; rewrite (tobs_env_reg c regs1 Tc r 8 8%bv eq_refl); exact (tm_s0 _ _ _ _ _ HM)).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (subst E; rewrite (tobs_env_reg c regs1 Tc r 22 22%bv eq_refl); exact (tm_s6 _ _ _ _ _ HM)).
assert (E18 : ew E 18 = Z_to_bv 64 (ts c - so)) by (subst E; rewrite (tobs_env_reg c regs1 Tc r 18 18%bv eq_refl); exact H18).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (UBx : U E TBx = SHADOW_OFF) by (unfold TBx; rewrite (U_atom E 22 SB E22) by (unfold SB; lia); reflexivity).
assert (Hed0 : ed E 0 = Tc) by reflexivity. assert (Hed1 : ed E 1 = tG c) by reflexivity.
assert (Hed2 : ed E 2 = DTC.sub Tc (48 * r) 48) by reflexivity.
assert (EE : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew E n = YK11.getr regs1 x) by (intros n x Hnx; subst E; apply tobs_env_reg; exact Hnx).
assert (HRO : regs_ok E tobs_sr regs1).
{ subst E; apply tobs_regs_ok; [exact (tm_s0 _ _ _ _ _ HM) | exact (tm_s5 _ _ _ _ _ HM) | exact (tm_s6 _ _ _ _ _ HM) | exact (tm_s8 _ _ _ _ _ HM) | lia | lia]. }
assert (HSTK : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H (tW c)) m1) (spZ regs1)) tobs_stk_chunks)
  by (subst E; apply tobs_stk_ok; exact (tm_frame _ _ _ _ _ HM)).
clearbody E.
assert (B2 : base_val E (Some 2%nat) = spZ regs1) by (cbn [base_val]; rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (Hspr : 2 ^ 46 + 96 <= spZ (tregs c) <= 2 ^ 47) by (unfold REAC_DISCO_TABLE_OBSERVE_STK in *; lia).
pose proof (Z.div_mod (tt c) 8 ltac:(lia)) as Dt. rewrite Ht8, Z.add_0_r in Dt.
pose proof (Z.div_mod (ts c) 8 ltac:(lia)) as Ds. rewrite Hs8, Z.add_0_r in Ds.
pose proof (Z.div_mod (spZ (tregs c)) 16 ltac:(lia)) as Dsp. rewrite Hal, Z.add_0_r in Dsp.
assert (Htr : 8 <= tt c <= 2 ^ 47 - 401) by lia. assert (Hsr : 8 <= ts c <= 2 ^ 47 - 25) by lia.
assert (B8 : base_val E (Some 8%nat) = tt c) by (apply VB; [exact E8 | lia]).
assert (U8 : U E (SOff 8 0) = tt c) by (apply U_atom; [exact E8 | lia]).
rewrite restrict_mkst_fx.
destruct Hso as [-> | ->]; destruct ent;
[ destruct (Hent eq_refl) as [Hr E19']
| clear Hent
| destruct (Hent eq_refl) as [Hr E19']
| clear Hent ];
try (assert (E19 : ew E 19 = Z_to_bv 64 (tt c + 48 * r)) by (rewrite (EE 19%nat 19%bv eq_refl); exact E19');
     assert (B19 : base_val E (Some 19%nat) = tt c + 48 * r) by (apply VB; [exact E19 | lia]);
     assert (U19 : U E (SOff 19 0) = tt c + 48 * r) by (apply U_atom; [exact E19 | lia]));
match goal with H : ew ?Ex 18 = Z_to_bv 64 (ts c - ?so) |- _ =>
  assert (B18 : base_val Ex (Some 18%nat) = ts c - so) by (apply VB; [exact H | lia]);
  assert (U18 : U Ex (SOff 18 0) = ts c - so) by (apply U_atom; [exact H | lia]) end;
(split;
 [ unfold tobs_ss; apply pa_entry_st_ok_full;
   [ exact HRO
   | vm_compute; reflexivity
   | unfold tobs_regions, R_stk, R_hdr, R_ent, R_sig; cbn [app];
     repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
     cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]
   | apply pairwise_disjoint_of_extents; unfold tobs_regions, R_stk, R_hdr, R_ent, R_sig, extent_of_region; cbn [app map YP09.r_base YP09.r_lo YP09.r_hi]
   | unfold tobs_facts; split; [|split; [exact I | exact I]]; cbn [f_atoms app atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2 Z.eqb] ]
 | unfold sh_ok, tobs_SH; cbn [app]; repeat apply Forall_cons; try apply Forall_nil ]);
rewrite ?B2, ?B8, ?B18; try rewrite B19;
first
[ solve [ split; [lia|]; split; [lia|]; split; [intros o Ho; lia | exact HSTK] ]
| solve [ split; [lia|]; split; [lia|]; split;
    [ intros o Ho; apply apresent_writable; apply Htpres; lia
    | apply Forall_cons; [|apply Forall_nil]; apply (chunk_cdata_garr8_s E _ (tt c) Tc 0 384 16); [exact HT | exact Hed0 | lia | lia | lia | lia] ] ]
| solve [ split; [lia|]; split; [lia|]; split;
    [ intros o Ho; apply apresent_writable; apply Htpres; lia
    | apply Forall_cons; [|apply Forall_nil]; apply (chunk_cdata_garr8_sub E _ (tt c) Tc 2 (48 * r) 48); [exact HT | exact Hed2 | lia | lia | lia | lia] ] ]
| solve [ split; [lia|]; split; [lia|]; split;
    [ intros o Ho; lia
    | apply Forall_cons; [|apply Forall_nil]; apply (chunk_cdata_garr8_s E _ (ts c) (tG c) 1 0 24); [exact HG | exact Hed1 | lia | lia | lia | lia] ] ]
| solve [ cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; rewrite ?Hsp; repeat split; lia ]
| solve [ rewrite E2, E8, ?E18, ?E19, E22, !unsigned_lit_small by (unfold SB; lia);
    repeat split; try lia;
    first [ rewrite Z.pow_0_r, Z.mod_1_r; reflexivity
          | change (2 ^ 4) with 16; replace (spZ (tregs c) - 96) with ((spZ (tregs c) / 16 - 6) * 16) by lia; apply Z_mod_mult
          | change (2 ^ 3) with 8; replace (tt c + 48 * r) with ((tt c / 8 + 6 * r) * 8) by lia; apply Z_mod_mult
          | change (2 ^ 3) with 8; replace (tt c) with ((tt c / 8) * 8) at 1 by lia; apply Z_mod_mult
          | change (2 ^ 3) with 8; replace (ts c - 0) with ((ts c / 8) * 8) by lia; apply Z_mod_mult
          | change (2 ^ 2) with 4; replace (ts c - -20) with ((2 * (ts c / 8) + 5) * 4) by lia; apply Z_mod_mult ] ]
| solve [ apply (shent_ok_of_range SEGS (w_H (tW c)) m1 E TBx 8 (tt c) 400 (tt c) 0 400 Htra UBx U8); try lia;
    intros x Hx; rewrite ?Z.min_l, ?Z.max_r in Hx by lia; unfold SHADOW_OFF; lia ]
| solve [ apply (shent_ok_of_range SEGS (w_H (tW c)) m1 E TBx 19 (tt c) 400 (tt c + 48 * r) 0 48 Htra UBx U19); try lia;
    intros x Hx; rewrite ?Z.min_l, ?Z.max_r in Hx by lia; unfold SHADOW_OFF; lia ]
| solve [ apply (shent_ok_of_range SEGS (w_H (tW c)) m1 E TBx 18 (ts c) 24 _ _ _ Hsra UBx U18); try lia;
    intros x Hx; rewrite ?Z.min_l, ?Z.max_r in Hx by lia; unfold SHADOW_OFF; lia ]
| match goal with |- ?g => idtac "GOALX" g end ].
all: fail.
Qed.
Lemma tobs_awr : forall c E ent so r, tpre c ->
  base_val E (Some 8%nat) = tt c -> (ent = true -> base_val E (Some 19%nat) = tt c + 48 * r /\ 0 <= r < 8) ->
  awr_ok E (tobs_regions ent so) (tSTK c) (tsp0 c) (tFP c) (ablocks B (tly c) (tS c)) (ablocks B (tlyc c) (tSc c))
    (tlyc c) (town c).
Proof.
intros c E ent so r HP B8 Hent a (rg & Hin & Ha).
unfold tobs_regions in Hin. destruct ent.
- destruct (Hent eq_refl) as [B19 Hr].
  cbn [In app] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]]; unfold R_stk, R_hdr, R_ent, R_sig in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ?B8, ?B19 in Ha; try lia;
  apply (proj1 (tp_tawr _ HP a ltac:(lia))).
- cbn [In app] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; unfold R_stk, R_hdr, R_sig in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ?B8 in Ha; try lia;
  apply (proj1 (tp_tawr _ HP a ltac:(lia))).
Qed.
Lemma ra_kept_band : forall (rd rd' : Z -> option Z) a n,
  (forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n HK Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. apply HK. unfold shadow_of_addr. assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma hull_kept_band : forall (rd rd' : Z -> option Z) a n,
  (forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof.
intros rd rd' a n HK Ha Han Hn HV s Hs. rewrite HK; [exact (HV s Hs)|]. unfold shadow_addr, SHADOW_OFF in *.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (a + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + a / 8) 8 ltac:(lia)). pose proof (Z.mul_div_le (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z_div_mod_eq_full (2147450880 + a / 8) 8). pose proof (Z.mod_pos_bound (2147450880 + a / 8) 8 ltac:(lia)).
pose proof (Z_div_mod_eq_full (2147450880 + (a + n - 1) / 8) 8). pose proof (Z.mod_pos_bound (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma tobs_t_not_img : forall c, tpre c -> forall a, tt c <= a < tt c + 400 -> ~ in_img SEGS a.
Proof.
intros c HP a Ha Himg. pose proof (pa_segs_low a Himg) as Hlow.
pose proof (tp_J _ HP) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & _) & _).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
destruct (proj1 (tp_tawr _ HP a Ha)) as [Hw | [[_ (b & n & Hin & Hb)] | [(b & n & Hin & _ & Hb) | (cid & pos & Hin & Hz)]]].
- lia.
- exact (blk_img SEGS B LAWS _ _ _ _ _ b n a HAR Hin Hb Himg).
- exact (blk_img SEGS B LAWS _ _ _ _ _ b n a HAR Hin Hb Himg).
- assert (Hin' : In (cid, pos) (frames (tSc c))) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
  destruct Hz as [Hz | Hz]; unfold in_zr, frame_rng in Hz; cbn [fst snd] in Hz.
  + exact (frm_img SEGS B LAWS _ _ _ _ _ cid pos a HAR Hin' Hz Himg).
  + unfold shadow_addr, SHADOW_OFF in Hz.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin') as (Hf4096 & _).
    pose proof (Z.div_pos (frame_addr (tlyc c) cid pos) 8 ltac:(lia) ltac:(lia)) as Hd.
    rewrite C5 in Hlow. lia.
Qed.
Lemma tobs_m_step : forall c regs1 m1 md1 Tc regs2 m2 md2 Tc',
  tpre c -> tobs_m c regs1 m1 md1 Tc ->
  ajournal SEGS B (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c) (tW0 c) (tmem0 c) (tmd0 c) (town c)
    (tlyc c) (tSc c) (tW c) m2 md2 (tk c) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tt c <= a < tt c + 400) -> ~ (spZ regs1 - 8192 <= a < spZ regs1) ->
     aview SEGS (w_H (tW c)) m2 a = aview SEGS (w_H (tW c)) m1 a) ->
  (forall a, apresent (w_H (tW c)) m1 a -> apresent (w_H (tW c)) m2 a) ->
  garr8 SEGS (mrestrict (w_H (tW c)) m2) (tt c) (map (fun b : byte => bv_unsigned b) Tc') -> length Tc' = 400%nat ->
  (forall r : Z, In r [2; 3; 4; 8; 9; 20; 21; 22; 24; 27] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs1 (Z_to_bv 5 r)) ->
  tobs_m c regs2 m2 md2 Tc'.
Proof.
intros c regs1 m1 md1 Tc regs2 m2 md2 Tc' HP HM HJ2 Hstep Hgrow HT' HTl' Hregs.
pose proof (tp_J _ HP) as HJc. pose proof HJc as (HARc & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (tp_wlo _ HP) as Hwlo. pose proof (tp_whi _ HP) as Hwhi.
pose proof (tp_t0 _ HP) as Ht0. pose proof (tp_tam _ HP) as Htam. pose proof (tp_twin _ HP) as Htwin.
pose proof (tp_s0 _ HP) as Hs0. pose proof (tp_sam _ HP) as Hsam. pose proof (tp_swin _ HP) as Hswin.
pose proof (tp_st _ HP) as Hst. pose proof (tp_Gl _ HP) as HGl.
pose proof (tm_sp _ _ _ _ _ HM) as Hsp.
assert (STK : REAC_DISCO_TABLE_OBSERVE_STK = 8288) by reflexivity. rewrite STK in Hwlo, Htwin, Hswin.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam, Hsam.
assert (Hwin : alloc_ceiling <= spZ regs1 - 8192) by lia.
assert (HspZ : spZ regs2 = spZ regs1) by (unfold spZ; f_equal; exact (Hregs 2 ltac:(cbn; lia))).
assert (Hband : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 ->
  aview SEGS (w_H (tW c)) m2 s = aview SEGS (w_H (tW c)) m1 s).
{ intros s0 Hs0'. apply Hstep; unfold SHADOW_OFF in *; lia. }
constructor.
- exact HJ2.
- rewrite HspZ. exact (tm_sp _ _ _ _ _ HM).
- etransitivity; [exact (Hregs 3 ltac:(cbn; lia)) | exact (tm_gp _ _ _ _ _ HM)].
- etransitivity; [exact (Hregs 4 ltac:(cbn; lia)) | exact (tm_tp _ _ _ _ _ HM)].
- etransitivity; [exact (Hregs 27 ltac:(cbn; lia)) | exact (tm_s11 _ _ _ _ _ HM)].
- etransitivity; [exact (Hregs 8 ltac:(cbn; lia)) | exact (tm_s0 _ _ _ _ _ HM)].
- etransitivity; [exact (Hregs 9 ltac:(cbn; lia)) | exact (tm_s1 _ _ _ _ _ HM)].
- etransitivity; [exact (Hregs 20 ltac:(cbn; lia)) | exact (tm_s4 _ _ _ _ _ HM)].
- etransitivity; [exact (Hregs 21 ltac:(cbn; lia)) | exact (tm_s5 _ _ _ _ _ HM)].
- etransitivity; [exact (Hregs 22 ltac:(cbn; lia)) | exact (tm_s6 _ _ _ _ _ HM)].
- etransitivity; [exact (Hregs 24 ltac:(cbn; lia)) | exact (tm_s8 _ _ _ _ _ HM)].
- rewrite HspZ. pose proof (tm_frame _ _ _ _ _ HM) as HF. unfold tobs_frame in *.
  rewrite Forall_forall in HF |- *. intros p Hp. pose proof (HF p Hp) as Hv.
  assert (Hp' : 0 <= fst p <= 88) by (unfold TS in Hp; cbn in Hp; repeat (destruct Hp as [<-|Hp]; [cbn; lia|]); destruct Hp).
  eapply val_mem_aview_kept_x; [|exact Hv]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply Hstep; lia.
- exact HT'.
- exact HTl'.
- eapply garr8_aview_kept; [|exact (tm_G _ _ _ _ _ HM)]. intros x Hx. rewrite length_map, HGl in Hx. change (Z.of_nat 24) with 24 in Hx. apply Hstep; lia.
- eapply ra_kept_band; [exact Hband | lia | lia | exact (tm_tra _ _ _ _ _ HM)].
- eapply ra_kept_band; [exact Hband | lia | lia | exact (tm_sra _ _ _ _ _ HM)].
- eapply hull_kept_band; [exact Hband | lia | lia | lia | exact (tm_thull _ _ _ _ _ HM)].
- eapply hull_kept_band; [exact Hband | lia | lia | lia | exact (tm_shull _ _ _ _ _ HM)].
- intros a Ha. apply Hgrow. exact (tm_tpres _ _ _ _ _ HM a Ha).
- intros a Ha. apply Hgrow. exact (tm_spres _ _ _ _ _ HM a Ha).
- pose proof (tm_kept _ _ _ _ _ HM) as HK. unfold tobs_kept, treac_disco_table_observe_kept in *.
  rewrite STK in *.
  destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw Ht. rewrite Hstep by lia. exact (K1 a Ha Hw Ht).
  + intros b m i Hb Hi Ht. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hb) as (_ & Hb4096 & Hbceil & _).
    rewrite Hstep by lia. exact (K2 b m i Hb Hi Ht).
  + intros a Himg Hno Herr. pose proof (pa_segs_low a Himg) as Hlow. rewrite C5 in Hlow.
    destruct (Z_lt_le_dec a (tt c)) as [Hlt|Hge]; [|destruct (Z_lt_le_dec a (tt c + 400)) as [Hlt2|Hge2]].
    * rewrite Hstep by lia. exact (K3 a Himg Hno Herr).
    * exfalso. exact (tobs_t_not_img c HP a ltac:(lia) Himg).
    * rewrite Hstep by lia. exact (K3 a Himg Hno Herr).
  + intros cid pos a Hin Hz Ht. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HARc Hin) as (Hf4096 & Hfceil & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfb.
    assert (Hfa : 0 <= a < alloc_ceiling \/ SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
    { destruct Hz as [Hz | Hz]; unfold in_zr, frame_rng, shadow_addr in Hz; cbn [fst snd] in Hz; [left; lia | right].
      pose proof (Z.div_pos (frame_addr (tlyc c) cid pos) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.mul_div_le (frame_addr (tlyc c) cid pos) 8 ltac:(lia)).
      pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)). unfold SHADOW_OFF in *. lia. }
    rewrite Hstep; [exact (K4 cid pos a Hin Hz Ht) | unfold SHADOW_OFF in Hfa; lia | exact Ht | unfold SHADOW_OFF in Hfa; lia].
  + intros a Ha Hw Hp. apply Hgrow. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply Hpres2. lia.
Qed.
Lemma garr8_of_mbytes : forall m p (L : list byte),
  (forall i, (i < length L)%nat -> mbyte SEGS m (p + Z.of_nat i) = Some (nth i L (Z_to_bv 8 0))) ->
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L).
Proof.
intros m p L H j Hj. rewrite length_map in Hj.
rewrite (nth_indep _ _ (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj). rewrite map_nth.
pose proof (bv_unsigned_in_range 8 (nth j L (Z_to_bv 8 0))) as R. change (bv_modulus 8) with 256 in R.
split; [|exact R].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, (H j Hj).
rewrite le_byte_1_0 by exact R. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma aview_of_garr8 : forall H m p (L : list byte) k,
  garr8 SEGS (mrestrict H m) p (map (fun b : byte => bv_unsigned b) L) -> (k < length L)%nat ->
  aview SEGS H m (p + Z.of_nat k) = Some (bv_unsigned (nth k L (Z_to_bv 8 0))).
Proof. intros H m p L k HG Hk. unfold aview. rewrite (garr8_mbyte _ _ _ _ HG Hk). reflexivity. Qed.
Definition cagree (E : env) (b lo : Z) (L : list byte) (ch : YP09.chunk) : Prop :=
  forall i, 0 <= i < YP09.c_len ch ->
  YP09.cbyte SEGS E (b + YP09.c_off ch) (YP09.c_val ch) i = nth_error L (Z.to_nat (YP09.c_off ch + i - lo)).
Definition covers_b (cs : list YP09.chunk) (lo hi : Z) : bool :=
  forallb (fun k => existsb (fun ch => (YP09.c_off ch <=? lo + Z.of_nat k) && (lo + Z.of_nat k <? YP09.c_off ch + YP09.c_len ch)) cs)
    (seq 0 (Z.to_nat (hi - lo))).
Lemma covers_b_ok : forall cs lo hi, covers_b cs lo hi = true ->
  forall i, lo <= i < hi -> exists ch, In ch cs /\ YP09.c_off ch <= i < YP09.c_off ch + YP09.c_len ch.
Proof.
intros cs lo hi H i Hi. unfold covers_b in H. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)). apply existsb_exists in H as (ch & Hin & Hc).
exists ch. split; [exact Hin|]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma region_bytes : forall E m n lo hi wlo whi cs b L,
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> base_val E (Some n) = b ->
  covers_b cs lo hi = true -> Forall (cagree E b lo L) cs ->
  forall i, lo <= i < hi -> mbyte SEGS m (b + i) = nth_error L (Z.to_nat (i - lo)).
Proof.
intros E m n lo hi wlo whi cs b L (_ & _ & _ & Hcs) Hb Hcov Hag i Hi.
cbn [YP09.r_base YP09.r_chunks] in Hcs. rewrite Hb in Hcs.
destruct (covers_b_ok cs lo hi Hcov i Hi) as (ch & Hin & Hr).
rewrite Forall_forall in Hcs, Hag.
destruct (Hcs ch Hin (i - YP09.c_off ch) ltac:(lia)) as (bt & Hb1 & Hb2).
replace (b + i) with (b + YP09.c_off ch + (i - YP09.c_off ch)) by lia. rewrite Hb2, <- Hb1.
rewrite (Hag ch Hin (i - YP09.c_off ch) ltac:(lia)). f_equal. f_equal. lia.
Qed.
Lemma garr8_exit : forall m m' p (L L' : list byte) (inW : Z -> bool),
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L) -> length L' = length L ->
  (forall i, 0 <= i < Z.of_nat (length L) -> inW i = false -> mbyte SEGS m' (p + i) = mbyte SEGS m (p + i)) ->
  (forall i, 0 <= i < Z.of_nat (length L) -> inW i = false -> nth_error L' (Z.to_nat i) = nth_error L (Z.to_nat i)) ->
  (forall i, 0 <= i < Z.of_nat (length L) -> inW i = true -> mbyte SEGS m' (p + i) = nth_error L' (Z.to_nat i)) ->
  garr8 SEGS m' p (map (fun b : byte => bv_unsigned b) L').
Proof.
intros m m' p L L' inW HG HL Hout HLo Hin. apply garr8_of_mbytes. intros i Hi.
assert (Hn : nth_error L' i = Some (nth i L' (Z_to_bv 8 0))) by (apply nth_error_nth'; exact Hi).
destruct (inW (Z.of_nat i)) eqn:Hw.
- rewrite (Hin (Z.of_nat i) ltac:(lia) Hw). rewrite Nat2Z.id. exact Hn.
- rewrite (Hout (Z.of_nat i) ltac:(lia) Hw). rewrite (garr8_mbyte _ _ _ i HG ltac:(lia)).
  pose proof (HLo (Z.of_nat i) ltac:(lia) Hw) as E. rewrite Nat2Z.id in E. rewrite Hn in E.
  assert (Hn2 : nth_error L i = Some (nth i L (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
  rewrite Hn2 in E. injection E as E. rewrite E. reflexivity.
Qed.
Lemma apresent_grows : forall H (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a HG [Hh [b Hb]]. split; [exact Hh|].
pose proof (HG (Z_to_bv 64 a)) as X. unfold mrestrict in X. rewrite Hh, Hb in X. cbv iota in X.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply X; [discriminate | reflexivity]].
Qed.
Lemma tobs_frame_out : forall c E ent so r (m m' : word -> option byte) a,
  frame_of E (tobs_regions ent so) m m' -> base_val E (Some 8%nat) = tt c ->
  (ent = true -> base_val E (Some 19%nat) = tt c + 48 * r) -> 0 <= a < 2 ^ 64 ->
  ~ (tt c + 384 <= a < tt c + 400) -> (ent = true -> ~ (tt c + 48 * r <= a < tt c + 48 * r + 48)) ->
  mbyte SEGS m' a = mbyte SEGS m a.
Proof.
intros c E ent so r m m' a HF B8 B19 Ha Hh He. apply (mbyte_of_frame_x SEGS E _ m m' a HF Ha).
intros rg Hin. unfold tobs_regions in Hin. destruct ent.
- specialize (B19 eq_refl). specialize (He eq_refl).
  cbn [In app] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]]; unfold R_stk, R_hdr, R_ent, R_sig;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite ?B8, ?B19; lia.
- cbn [In app] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; unfold R_stk, R_hdr, R_sig;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite ?B8; lia.
Qed.
Lemma tobs_exit_run : forall c regs1 m1 md1 Tc E ent so r regs2 m2 md2 Tc',
  tpre c -> tobs_m c regs1 m1 md1 Tc ->
  base_val E (Some 8%nat) = tt c -> (ent = true -> base_val E (Some 19%nat) = tt c + 48 * r /\ 0 <= r < 8) ->
  frame_of E (tobs_regions ent so) (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) m2) ->
  mem_grows (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) m2) ->
  ajournal SEGS B (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c) (tW0 c) (tmem0 c) (tmd0 c) (town c)
    (tlyc c) (tSc c) (tW c) m2 md2 (tk c) ->
  length Tc' = 400%nat ->
  (forall i, 0 <= i < 400 -> ~ (384 <= i < 400) -> (ent = true -> ~ (48 * r <= i < 48 * r + 48)) ->
     nth_error Tc' (Z.to_nat i) = nth_error Tc (Z.to_nat i)) ->
  (forall i, 384 <= i < 400 -> mbyte SEGS (mrestrict (w_H (tW c)) m2) (tt c + i) = nth_error Tc' (Z.to_nat i)) ->
  (ent = true -> forall i, 48 * r <= i < 48 * r + 48 ->
     mbyte SEGS (mrestrict (w_H (tW c)) m2) (tt c + i) = nth_error Tc' (Z.to_nat i)) ->
  (forall q : Z, In q [2; 3; 4; 8; 9; 20; 21; 22; 24; 27] -> YK11.getr regs2 (Z_to_bv 5 q) = YK11.getr regs1 (Z_to_bv 5 q)) ->
  tobs_m c regs2 m2 md2 Tc'.
Proof.
intros c regs1 m1 md1 Tc E ent so r regs2 m2 md2 Tc' HP HM B8 Hent HF HG HJ2 HL' Hout Hhdr Hent2 Hregs.
pose proof (tp_t0 _ HP) as Ht0. pose proof (tp_t63 _ HP) as Ht63. pose proof (tm_Tl _ _ _ _ _ HM) as HTl.
assert (B19 : ent = true -> base_val E (Some 19%nat) = tt c + 48 * r) by (intros X; exact (proj1 (Hent X))).
assert (Hr : ent = true -> 0 <= r < 8) by (intros X; exact (proj2 (Hent X))).
apply (tobs_m_step c regs1 m1 md1 Tc regs2 m2 md2 Tc' HP HM HJ2).
- intros a Ha Ht Hw. unfold aview. f_equal.
  apply (tobs_frame_out c E ent so r _ _ a HF B8 B19 Ha); [lia | intros X; specialize (Hr X); lia].
- intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
- apply (garr8_exit (mrestrict (w_H (tW c)) m1) _ (tt c) Tc Tc'
    (fun i => ((384 <=? i) && (i <? 400)) || (ent && (48 * r <=? i) && (i <? 48 * r + 48)))
    (tm_T _ _ _ _ _ HM) ltac:(rewrite HL', HTl; reflexivity)).
  + intros i Hi Hw. apply orb_false_iff in Hw as [Hw1 Hw2].
    apply (tobs_frame_out c E ent so r _ _ (tt c + i) HF B8 B19); [lia | |].
    * rewrite HTl in Hi. intros X. apply andb_false_iff in Hw1 as [Y|Y]; [apply Z.leb_gt in Y | apply Z.ltb_ge in Y]; lia.
    * intros X. rewrite X in Hw2. cbn [andb] in Hw2. apply andb_false_iff in Hw2 as [Y|Y]; [apply Z.leb_gt in Y | apply Z.ltb_ge in Y]; lia.
  + intros i Hi Hw. apply orb_false_iff in Hw as [Hw1 Hw2]. rewrite HTl in Hi. apply Hout; [lia | |].
    * intros X. apply andb_false_iff in Hw1 as [Y|Y]; [apply Z.leb_gt in Y | apply Z.ltb_ge in Y]; lia.
    * intros X Y. rewrite X in Hw2. cbn [andb] in Hw2. apply andb_false_iff in Hw2 as [Z1|Z1]; [apply Z.leb_gt in Z1 | apply Z.ltb_ge in Z1]; lia.
  + intros i Hi Hw. apply orb_true_iff in Hw as [Hw|Hw].
    * apply andb_prop in Hw as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.ltb_lt in Y2. apply Hhdr. lia.
    * apply andb_prop in Hw as [Y0 Y2]. apply andb_prop in Y0 as [Y0 Y1]. apply Z.leb_le in Y1. apply Z.ltb_lt in Y2.
      apply (Hent2 Y0). lia.
- exact HL'.
- exact Hregs.
Qed.
Definition cfgB (pc : Z) (regs : bvmap 5 word) (m : word -> option byte) (md : Model) : config :=
  mkCfg (YK11.mkst regs (Z_to_bv 64 (BASE + pc)) m (YK11.seg_rom SEGS)) md.
Definition tnone (c : tctx) : Prop :=
  forall j, 0 <= j < DTC.n_of (tT c) -> DTC.mac_of (tT c) j <> DTC.s_mac (tG c).
Definition tfound (c : tctx) (r : Z) : Prop :=
  0 <= r < DTC.n_of (tT c) /\ DTC.mac_of (tT c) r = DTC.s_mac (tG c) /\
  (forall j, 0 <= j < r -> DTC.mac_of (tT c) j <> DTC.s_mac (tG c)).
Definition tf1 (c : tctx) (r : Z) : bool := RDO.cR (tT c) (tG c) r.
Definition tf2 (c : tctx) (r : Z) : bool := tf1 c r || RDO.cD (tT c) (tG c) r.
Definition tf3 (c : tctx) (r : Z) : bool := tf2 c r || RDO.cS (tT c) (tG c) r.
Definition tf4 (c : tctx) (r : Z) : bool := tf3 c r || RDO.cF (tT c) (tG c) r.
Definition tf5 (c : tctx) (r : Z) : bool := tf4 c r || RDO.cC (tT c) (tG c) r.
Definition SegRet (c : tctx) : Prop :=
  forall regs1 m1 md1 Tc so ret, tpre c -> tobs_m c regs1 m1 md1 Tc ->
  (so = 0 \/ so = -20) -> YK11.getr regs1 18 = w64 (ts c - so) -> YK11.getr regs1 10 = w64 ret ->
  RDOC.observe_model (tT c) (tG c) (tow c) (tnow c) Tc ret ->
  SRr SEGS (tW c) (cfgB 0x55f0 regs1 m1 md1) (tpost c).
Definition SegSeq (c : tctx) : Prop :=
  forall regs1 m1 md1 Tc so ret, tpre c -> tobs_m c regs1 m1 md1 Tc ->
  (so = 0 \/ so = -20) -> YK11.getr regs1 18 = w64 (ts c - so) -> YK11.getr regs1 10 = w64 ret ->
  RDOC.observe_model (tT c) (tG c) (tow c) (tnow c) (DTC.upd Tc 392 (Z_to_le_bytes 4 (DTC.seq_of Tc + 1))) ret ->
  SRr SEGS (tW c) (cfgB 0x55d0 regs1 m1 md1) (tpost c).
Definition SegK6 (c : tctx) : Prop :=
  forall regs1 m1 md1 r, tpre c -> tobs_m c regs1 m1 md1 (RDO.kF (tT c) (tG c) (tnow c) r) ->
  YK11.getr regs1 18 = w64 (ts c + 20) -> YK11.getr regs1 19 = w64 (tt c + 48 * r) -> YK11.getr regs1 12 = w64 (Z.b2z (tf5 c r)) ->
  tfound c r -> RDO.cO (tT c) (tow c) r = false ->
  SRr SEGS (tW c) (cfgB 0x53bc regs1 m1 md1) (tpost c).
Definition SegK5 (c : tctx) : Prop :=
  forall regs1 m1 md1 r, tpre c -> tobs_m c regs1 m1 md1 (RDO.kF (tT c) (tG c) (tnow c) r) ->
  YK11.getr regs1 18 = w64 (ts c + 20) -> YK11.getr regs1 19 = w64 (tt c + 48 * r) -> YK11.getr regs1 12 = w64 (Z.b2z (tf5 c r)) ->
  tfound c r -> SRr SEGS (tW c) (cfgB 0x539c regs1 m1 md1) (tpost c).
Definition SegK4 (c : tctx) : Prop :=
  forall regs1 m1 md1 r, tpre c -> tobs_m c regs1 m1 md1 (RDO.kE (tT c) (tG c) (tnow c) r) ->
  YK11.getr regs1 18 = w64 (ts c) -> YK11.getr regs1 19 = w64 (tt c + 48 * r) -> YK11.getr regs1 12 = w64 (Z.b2z (tf4 c r)) ->
  tfound c r -> SRr SEGS (tW c) (cfgB 0x5358 regs1 m1 md1) (tpost c).
Definition SegK3 (c : tctx) : Prop :=
  forall regs1 m1 md1 r, tpre c -> tobs_m c regs1 m1 md1 (RDO.kD (tT c) (tG c) (tnow c) r) ->
  YK11.getr regs1 18 = w64 (ts c) -> YK11.getr regs1 19 = w64 (tt c + 48 * r) -> YK11.getr regs1 12 = w64 (Z.b2z (tf3 c r)) ->
  tfound c r -> SRr SEGS (tW c) (cfgB 0x5310 regs1 m1 md1) (tpost c).
Definition SegK2 (c : tctx) : Prop :=
  forall regs1 m1 md1 r, tpre c -> tobs_m c regs1 m1 md1 (RDO.kC (tT c) (tG c) (tnow c) r) ->
  YK11.getr regs1 18 = w64 (ts c) -> YK11.getr regs1 19 = w64 (tt c + 48 * r) -> YK11.getr regs1 12 = w64 (Z.b2z (tf2 c r)) ->
  tfound c r -> SRr SEGS (tW c) (cfgB 0x52c8 regs1 m1 md1) (tpost c).
Definition SegK1 (c : tctx) : Prop :=
  forall regs1 m1 md1 r, tpre c -> tobs_m c regs1 m1 md1 (RDO.kB (tT c) (tG c) (tnow c) r) ->
  YK11.getr regs1 18 = w64 (ts c) -> YK11.getr regs1 19 = w64 (tt c + 48 * r) -> YK11.getr regs1 12 = w64 (Z.b2z (tf1 c r)) ->
  tfound c r -> SRr SEGS (tW c) (cfgB 0x51b4 regs1 m1 md1) (tpost c).
Definition SegFound (c : tctx) : Prop :=
  forall regs1 m1 md1 r, tpre c -> tobs_m c regs1 m1 md1 (tT c) ->
  YK11.getr regs1 18 = w64 (ts c) -> YK11.getr regs1 19 = w64 (tt c + 48 * r) ->
  tfound c r -> SRr SEGS (tW c) (cfgB 0x514c regs1 m1 md1) (tpost c).
Definition SegNone (c : tctx) : Prop :=
  forall regs1 m1 md1, tpre c -> tobs_m c regs1 m1 md1 (tT c) ->
  YK11.getr regs1 18 = w64 (ts c) -> YK11.getr regs1 23 = w64 (DTC.n_of (tT c)) ->
  tnone c -> SRr SEGS (tW c) (cfgB 0x53c4 regs1 m1 md1) (tpost c).
Definition SegNew (c : tctx) : Prop :=
  forall regs1 m1 md1, tpre c -> tobs_m c regs1 m1 md1 (tT c) ->
  YK11.getr regs1 18 = w64 (ts c) -> YK11.getr regs1 23 = w64 (DTC.n_of (tT c)) ->
  tnone c -> DTC.n_of (tT c) < 8 -> SRr SEGS (tW c) (cfgB 0x53f0 regs1 m1 md1) (tpost c).
Definition SegLoop (c : tctx) : Prop :=
  forall regs1 m1 md1 j, tpre c -> tobs_m c regs1 m1 md1 (tT c) ->
  YK11.getr regs1 18 = w64 (ts c) -> YK11.getr regs1 23 = w64 (DTC.n_of (tT c)) ->
  YK11.getr regs1 25 = w64 (48 * j) -> YK11.getr regs1 26 = w64 (48 * DTC.n_of (tT c)) ->
  0 <= j < DTC.n_of (tT c) -> (forall j', 0 <= j' < j -> DTC.mac_of (tT c) j' <> DTC.s_mac (tG c)) ->
  SRr SEGS (tW c) (cfgB 0x5128 regs1 m1 md1) (tpost c).
End h.
End f.
End d.
