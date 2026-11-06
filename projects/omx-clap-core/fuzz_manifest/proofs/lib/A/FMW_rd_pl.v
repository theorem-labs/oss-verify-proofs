(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:49-57;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACan.v:337-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-147, 156-161;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:193-195, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg1.v, with its module paths, module names and numbers changed; 459 of its 550 lines of code are new or changed and 365 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/SbDecSeg1.v, with its module paths, module names and numbers changed; 1841 of its 1900 lines of code are new or changed and 491 lines of the source are left out. *)
(* lv2_locate_manifest_readings: plain_local's loop at 0x81fc8 (lv2_locate.c:48-51, 139-145), the segment statement
   rd_seg_PL of lib/A/FMW_rd_cuts.v: rd_PL_holds (FMW_rd_top.v's SEG_PL).
   The walk, cut at four pcs, each with its own symbolic state built from Props:
     A 0x81fc8 (rd_PL): the shadow check of local + q, the byte c = ub[o + q], isalnum (PC_isalnum, ra 0x81fe4);
     B 0x81fe4 (pl_from_B): isalnum's answer, then c - 45 >u 50 and bit (c - 45) of RD_MASK2 (pl_cls_*, decided
       over all 256 bytes) -> P or N;
     P 0x82004 (pl_from_P): s9++, s10--, s5++; bytes left -> back to A at q + 1 (rd_seg_PL); else s5 = 1 and
       read_again > 15 -> RD_R (readings_scan sc_cnt), or ++*readings (the 8-byte check of rp from the stack's
       zero shadow) and has_prefixed (0x82130, ra 0x82070) -> C;
     N 0x82028 (pl_from_N, RD_CONT): the name is not plain, the declaration does not match -> RD_L at S close
       (sc_nomatch);
     C 0x82070 (pl_from_C): has_prefixed's answer: a token -> RD_R (sc_tok), else read_again + 1 -> RD_L (sc_next).
   Memory across a step: pl_win / pl_same (only the callee's stack, the read_again slot and *readings change),
   pl_com_kept / pl_mid_kept / pl_PL_kept; across has_prefixed: pl_mid_hp (its journal, fm_img_facts for the
   strings). The pure model steps are copies of lib/Prog/readings_scan.v:177-310 (that file imports lib/Lib). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YG0s YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_rd_cuts FMW_rd_ret.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ======== pure list and model helpers (lib/Prog/readings_scan.v:177-310, copied: that file imports lib/Lib, whose
   getr / mkst / seg_rom shadow the core's) ======== *)

Lemma pl_firstn_S : forall (l : list Z) k, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l 0].
Proof.
  induction l as [|x l IH]; intros [|k] Hk; cbn in *; try lia; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Lemma pl_forallb_false : forall f (l : list Z) k, (k < length l)%nat -> f (nth k l 0) = false -> forallb f l = false.
Proof.
  induction l as [|x l IH]; intros [|k] Hk Hf; cbn in *; try lia.
  - rewrite Hf. reflexivity.
  - rewrite (IH k ltac:(lia) Hf). apply andb_false_r.
Qed.

Lemma pl_forallb_S : forall f (l : list Z) k, (k < length l)%nat ->
  forallb f (firstn k l) = true -> f (nth k l 0) = true -> forallb f (firstn (S k) l) = true.
Proof.
  intros f l k Hk H1 H2. rewrite pl_firstn_S by lia. rewrite forallb_app, H1. cbn [forallb].
  rewrite H2. reflexivity.
Qed.

Lemma pl_nth_skipn : forall o (l : list Z) k, nth k (skipn o l) 0 = nth (o + k) l 0.
Proof.
  induction o as [|o IH]; intros l k; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct k; reflexivity | apply IH].
Qed.

Lemma pl_plain_name : forall (l : list Z), l <> [] -> last l 0 <> 46 -> plain_name l = forallb plain_ok l.
Proof.
  intros [|x l] H1 H2; [congruence|]. cbn [plain_name].
  destruct (Z.eqb_spec (last (x :: l) 0) 46); [congruence | reflexivity].
Qed.

Lemma pl_matches : forall (t u : list Z) ns o, (o < length u)%nat -> firstn o (skipn ns t) = firstn o u ->
  matches t u ns o = plain_name (skipn o u).
Proof.
  intros t u ns o Ho He. unfold matches.
  rewrite (proj2 (Nat.ltb_lt _ _) Ho), (proj2 (zl_eqb_eq _ _) He). reflexivity.
Qed.

Lemma pl_decl_found : forall (t : list Z) i s11 p1 p2 p3 o,
  head t i = Some (i + s11)%nat -> is_space (byte_at t (i + s11)) = true ->
  p1 = (i + s11 + count_while is_space (skipn (i + s11) t))%nat ->
  p2 = (p1 + count_while name_ok (skipn p1 t))%nat -> byte_at t p2 = 58 ->
  p3 = (S p2 + count_while is_space (skipn (S p2) t))%nat -> byte_at t p3 = 60 ->
  find_idx (fun c => c =? 62) (skipn (S p3) t) = Some o ->
  decl t i = DFound p1 (p2 - p1) (S p3) o (S p3 + o).
Proof.
  intros t i s11 p1 p2 p3 o Hh Hs E1 E2 Hc E3 Hl Hf.
  unfold decl. rewrite Hh, Hs. cbn [negb]. cbv beta iota zeta.
  rewrite <- E1, <- E2, Hc, Z.eqb_refl. cbn [negb]. cbv beta iota zeta.
  rewrite <- E3, Hl, Z.eqb_refl. cbn [negb]. cbv beta iota zeta. rewrite Hf. reflexivity.
Qed.

Lemma pl_sc_nomatch : forall t u i d f name nl ns nl2 close, (i < length t)%nat ->
  decl t i = DFound name nl ns nl2 close -> matches t u ns nl2 = false ->
  scan t u i d (S f) = scan t u (S close) d f /\ readings t u i d (S f) = readings t u (S close) d f.
Proof.
  intros t u i d f name nl ns nl2 close H D M. cbn [scan readings].
  rewrite (proj2 (Nat.leb_gt _ _) H), D, M. split; reflexivity.
Qed.

Lemma pl_sc_cnt : forall t u i d f name nl ns nl2 close, (i < length t)%nat ->
  decl t i = DFound name nl ns nl2 close -> matches t u ns nl2 = true -> (16 <= d)%nat ->
  scan t u i d (S f) = 1 /\ readings t u i d (S f) = O.
Proof.
  intros t u i d f name nl ns nl2 close H D M Hd. cbn [scan readings].
  rewrite (proj2 (Nat.leb_gt _ _) H), D, M, (proj2 (Nat.ltb_lt 16 (S d)) ltac:(lia)). split; reflexivity.
Qed.

Lemma pl_sc_tok : forall t u i d f name nl ns nl2 close, (i < length t)%nat ->
  decl t i = DFound name nl ns nl2 close -> matches t u ns nl2 = true -> (d < 16)%nat ->
  token t (firstn nl (skipn name t)) (skipn nl2 u) = true ->
  scan t u i d (S f) = 1 /\ readings t u i d (S f) = 1%nat.
Proof.
  intros t u i d f name nl ns nl2 close H D M Hd T. cbn [scan readings].
  rewrite (proj2 (Nat.leb_gt _ _) H), D, M, (proj2 (Nat.ltb_ge 16 (S d)) ltac:(lia)), T. split; reflexivity.
Qed.

Lemma pl_sc_next : forall t u i d f name nl ns nl2 close, (i < length t)%nat ->
  decl t i = DFound name nl ns nl2 close -> matches t u ns nl2 = true -> (d < 16)%nat ->
  token t (firstn nl (skipn name t)) (skipn nl2 u) = false ->
  scan t u i d (S f) = scan t u (S close) (S d) f /\
  readings t u i d (S f) = S (readings t u (S close) (S d) f).
Proof.
  intros t u i d f name nl ns nl2 close H D M Hd T. cbn [scan readings].
  rewrite (proj2 (Nat.leb_gt _ _) H), D, M, (proj2 (Nat.ltb_ge 16 (S d)) ltac:(lia)), T. split; reflexivity.
Qed.

Lemma pl_find_idx_lt : forall f (l : list Z) o, find_idx f l = Some o -> (o < length l)%nat.
Proof.
  intros f l. induction l as [|x l IH]; intros o H; cbn in H; [discriminate|].
  destruct (f x); [inversion H; cbn; lia|].
  destruct (find_idx f l) as [o'|] eqn:E; cbn in H; [|discriminate].
  inversion H; subst. cbn. specialize (IH o' eq_refl). lia.
Qed.

(* ======== the byte classification: isalnum, then c - 45 >u 50, then bit (c - 45) of RD_MASK2 ======== *)
Definition pl_b1 : sv := SOff 27 (-45).
Definition pl_b2 : sv := SAlu ALU_AND (SAlu ALU_SRL (SLit RD_MASK2) (SOff 27 (-45))) (SLit 1).
Definition pl_E00 : env := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => []).
Definition pl_Eat (n : nat) (c : Z) : env := ewset pl_E00 n (Z_to_bv 64 c).
Definition pl_D (n : nat) (cnd : branch_cond) (a b : sv) (c : Z) : bool :=
  branch_taken cnd (sv_denot (pl_Eat n c) a) (sv_denot (pl_Eat n c) b).

Lemma pl_D_of : forall n E c cnd a b, ew E n = Z_to_bv 64 c ->
  sv_atoms_in (Nat.eqb n) a = true -> sv_atoms_in (Nat.eqb n) b = true ->
  branch_taken cnd (sv_denot E a) (sv_denot E b) = pl_D n cnd a b c.
Proof.
  intros n E c cnd a b HE Ha Hb. unfold pl_D.
  assert (HA : env_agree_on (Nat.eqb n) E (pl_Eat n c)).
  { intros k Hk. apply Nat.eqb_eq in Hk. subst k. unfold pl_Eat. rewrite ew_ewset_same. symmetry. exact HE. }
  rewrite (sv_denot_agree_on _ _ _ a HA Ha), (sv_denot_agree_on _ _ _ b HA Hb). reflexivity.
Qed.

(* the read_again test at 0x8203c: blt 15, s8 *)
Lemma pl_D_d : forall dv, 0 <= dv <= 16 -> pl_D 24 BC_LT (SLit 15) (SOff 24 0) dv = (15 <? dv).
Proof.
  intros dv Hd.
  assert (H : forallb (fun z => Bool.eqb (pl_D 24 BC_LT (SLit 15) (SOff 24 0) z) (15 <? z))
    (map Z.of_nat (seq 0 17)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  specialize (H dv ltac:(apply in_map_iff; exists (Z.to_nat dv); split; [apply Z2Nat.id; lia | apply in_seq; lia])).
  cbn beta in H. destruct (pl_D 24 BC_LT (SLit 15) (SOff 24 0) dv), (15 <? dv); cbn in H; congruence.
Qed.

Definition pl_cls_ok (c : Z) : bool :=
  let d1 := pl_D 27 BC_LTU (SLit 50) pl_b1 c in
  let d2 := pl_D 27 BC_EQ pl_b2 (SLit 0) c in
  implb (negb (is_alnum c) && d1) (negb (plain_ok c)) &&
  implb (negb (is_alnum c) && negb d1 && d2) (negb (plain_ok c)) &&
  implb (negb (is_alnum c) && negb d1 && negb d2) (plain_ok c).

Lemma pl_cls_all : forall c, 0 <= c < 256 -> pl_cls_ok c = true.
Proof.
  intros c Hc.
  assert (H : forallb pl_cls_ok (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat c). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.

Ltac pl_cls_tac c Hc :=
  intros; pose proof (pl_cls_all c Hc) as X; unfold pl_cls_ok in X;
  repeat match goal with H : pl_D _ _ _ _ c = _ |- _ => rewrite H in X; clear H end;
  repeat match goal with H : is_alnum c = _ |- _ => rewrite H in X; clear H end;
  cbn [negb andb implb] in X; destruct (plain_ok c); first [reflexivity | discriminate X].

Lemma pl_alnum_plain : forall c, is_alnum c = true -> plain_ok c = true.
Proof. intros c H. unfold plain_ok. rewrite H. reflexivity. Qed.
Lemma pl_cls_far : forall c, 0 <= c < 256 -> is_alnum c = false ->
  pl_D 27 BC_LTU (SLit 50) pl_b1 c = true -> plain_ok c = false.
Proof. intros c Hc. pl_cls_tac c Hc. Qed.
Lemma pl_cls_bit0 : forall c, 0 <= c < 256 -> is_alnum c = false ->
  pl_D 27 BC_LTU (SLit 50) pl_b1 c = false -> pl_D 27 BC_EQ pl_b2 (SLit 0) c = true -> plain_ok c = false.
Proof. intros c Hc. pl_cls_tac c Hc. Qed.
Lemma pl_cls_bit1 : forall c, 0 <= c < 256 -> is_alnum c = false ->
  pl_D 27 BC_LTU (SLit 50) pl_b1 c = false -> pl_D 27 BC_EQ pl_b2 (SLit 0) c = false -> plain_ok c = true.
Proof. intros c Hc. pl_cls_tac c Hc. Qed.

(* ======== the cut states ======== *)
Definition PL_A : Z := 0x81fc8.   (* plain_local's head *)
Definition PL_B : Z := 0x81fe4.   (* after isalnum *)
Definition PL_P : Z := 0x82004.   (* the byte is plain *)
Definition PL_N : Z := 0x82028.   (* the byte is not plain: RD_CONT *)
Definition PL_C : Z := 0x82070.   (* after has_prefixed *)
Definition PL_Bx : sv := SOff 8 0.
Definition PL_Bspan : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).

(* A: atom 2 = F, atom 8 = the shadow base, atom 21 = local + q (s5 = s9), atom 32 = the byte *)
Definition pl_facts_A : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47 - 224) 4); (8%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (21%nat, mkAF 4096 (2 ^ 47 - 16) 0); (32%nat, mkAF 0 255 0)] [] [].
Definition pl_regsA : list sv := sr_set (sr_set sr_atoms 25%bv (SOff 21 0)) 20%bv (SOff 2 208).
Definition pl_byte : YP09.region := YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition ss_A : sstate := mkSS PL_A pl_regsA [pl_byte] None pl_facts_A.

(* B: atom 10 = isalnum's answer, 24 = d, 26 = n - q, 27 = the byte; the frame slots 0x18 (mask), 0x38 (local),
   0x40 (text) read-only, the counter cell at 208 and the read_again slot at 8 writable;
   atom 32 = local, 33 = text, 34 = *rp, 35 = read_again *)
Definition pl_facts_B : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47 - 224) 4); (8%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (21%nat, mkAF 4096 (2 ^ 47 - 16) 0); (24%nat, mkAF 0 16 0); (26%nat, mkAF 1 255 0);
           (27%nat, mkAF 0 255 0)] [] [].
Definition pl_fr_ro : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x18 0x48 0 0
    [YP09.mkChunk 0x18 (CVal 8 (SLit RD_MASK2)); YP09.mkChunk 0x38 (CVal 8 (SOff 32 0));
     YP09.mkChunk 0x40 (CVal 8 (SOff 33 0))].
Definition pl_fr_rp : YP09.region :=
  YP09.mkRegion (Some 2%nat) 208 216 208 216 [YP09.mkChunk 208 (CVal 8 (SOff 34 0))].
Definition pl_fr_d : YP09.region :=
  YP09.mkRegion (Some 2%nat) 8 16 8 16 [YP09.mkChunk 8 (CVal 8 (SOff 35 0))].
Definition pl_regsB : list sv := sr_set (sr_set sr_atoms 25%bv (SOff 21 0)) 20%bv (SOff 2 208).
Definition ss_BP (pc : Z) : sstate := mkSS pc pl_regsB [pl_fr_ro; pl_fr_rp; pl_fr_d] None pl_facts_B.

(* C: only the read_again slot matters *)
Definition pl_facts_C : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47 - 224) 4); (8%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (24%nat, mkAF 0 16 0)] [] [].
Definition ss_C : sstate := mkSS PL_C sr_atoms [pl_fr_d] None pl_facts_C.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

Lemma pl_chunk8 : forall E m b off (e : sv) v,
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs m (b + off) 8 v ->
  YP09.chunk_ok tfibsegs E m b (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros E m b off e v He Hv Hm. apply (chunk_ok_val tfibsegs E m b off 8%N e v He); [cbn; lia | cbn; lia | exact Hm].
Qed.

Lemma plA_entry : forall (W : world tfibsegs) regs mem F lq c,
  getr regs 2 = w64 F -> getr regs 8 = w64 SHADOW_OFF -> getr regs 20 = w64 (F + 208) ->
  getr regs 21 = w64 lq -> getr regs 25 = w64 lq ->
  2 ^ 46 <= F <= 2 ^ 47 - 224 -> F mod 16 = 0 -> 4096 <= lq <= 2 ^ 47 - 16 -> 0 <= c < 256 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) lq 1 c ->
  st_ok tfibsegs (Ereg regs [w64 c]) ss_A (restrict (w_H W) (mkst regs (Z_to_bv 64 PL_A) mem (seg_rom tfibsegs))).
Proof.
  intros W regs mem F lq c R2 R8 R20 R21 R25 HF HF16 Hlq Hc Vc.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs [w64 c]).
  assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
  assert (E8 : ew E 8 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
  assert (E21 : ew E 21 = w64 lq) by (unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
  assert (E32 : ew E 32 = w64 c) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
  assert (U2 : bv_unsigned (ew E 2) = F) by (rewrite E2; apply unsigned_lit_small; lia).
  assert (U8 : bv_unsigned (ew E 8) = SHADOW_OFF) by (rewrite E8; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U21 : bv_unsigned (ew E 21) = lq) by (rewrite E21; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
  unfold ss_A. apply (entry_st_ok_full tfibsegs); change (Ereg regs [w64 c]) with E.
  - unfold pl_regsA.
    repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg | ..];
      cbn [sv_denot]; rewrite ?Z.add_0_r;
      first [ rewrite U2; exact R20 | rewrite U21; exact R25 ].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold pl_byte, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U21.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs E _ lq 0 1%N (SOff 32 0) c);
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Vc.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pl_facts_A]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U8, U21, U32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; try lia.
Qed.

Lemma plB_entry : forall (W : world tfibsegs) pc regs mem F lq c vv dv s10v localv textv rpv dslot,
  getr regs 2 = w64 F -> getr regs 8 = w64 SHADOW_OFF -> getr regs 20 = w64 (F + 208) ->
  getr regs 21 = w64 lq -> getr regs 25 = w64 lq -> getr regs 24 = w64 dv -> getr regs 26 = w64 s10v ->
  getr regs 27 = w64 c -> getr regs 10 = w64 vv ->
  2 ^ 46 <= F <= 2 ^ 47 - 224 -> F mod 16 = 0 -> 4096 <= lq <= 2 ^ 47 - 16 -> 0 <= c < 256 ->
  0 <= dv <= 16 -> 1 <= s10v <= 255 ->
  0 <= localv < 2 ^ 64 -> 0 <= textv < 2 ^ 64 -> 0 <= rpv < 2 ^ 64 -> 0 <= dslot < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 0x18) 8 RD_MASK2 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 0x38) 8 localv ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 0x40) 8 textv ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 208) 8 rpv ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 8) 8 dslot ->
  (forall a, F + 208 <= a < F + 216 -> writable_at tfibsegs (mrestrict (w_H W) mem) a) ->
  (forall a, F + 8 <= a < F + 16 -> writable_at tfibsegs (mrestrict (w_H W) mem) a) ->
  st_ok tfibsegs (Ereg regs [w64 localv; w64 textv; w64 rpv; w64 dslot]) (ss_BP pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
  intros W pc regs mem F lq c vv dv s10v localv textv rpv dslot R2 R8 R20 R21 R25 R24 R26 R27 R10
    HF HF16 Hlq Hc Hdv Hs10 Hlocal Htext Hrp Hds V18 V38 V40 V208 V8 W208 W8.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs [w64 localv; w64 textv; w64 rpv; w64 dslot]).
  assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
  assert (E8 : ew E 8 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
  assert (E21 : ew E 21 = w64 lq) by (unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
  assert (E24 : ew E 24 = w64 dv) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (E26 : ew E 26 = w64 s10v) by (unfold E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  assert (E27 : ew E 27 = w64 c) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = w64 localv) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = w64 textv) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = w64 rpv) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = w64 dslot) by (unfold E; exact (ew_Ereg_extra regs _ 3)).
  assert (U2 : bv_unsigned (ew E 2) = F) by (rewrite E2; apply unsigned_lit_small; lia).
  assert (U8 : bv_unsigned (ew E 8) = SHADOW_OFF) by (rewrite E8; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U21 : bv_unsigned (ew E 21) = lq) by (rewrite E21; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = dv) by (rewrite E24; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = s10v) by (rewrite E26; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = c) by (rewrite E27; apply unsigned_lit_small; lia).
  unfold ss_BP. apply (entry_st_ok_full tfibsegs);
    change (Ereg regs [w64 localv; w64 textv; w64 rpv; w64 dslot]) with E.
  - unfold pl_regsB.
    repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg | ..];
      cbn [sv_denot]; rewrite ?Z.add_0_r;
      first [ rewrite U2; exact R20 | rewrite U21; exact R25 ].
  - vm_compute. reflexivity.
  - unfold pl_fr_ro, pl_fr_rp, pl_fr_d.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U2.
    + split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (pl_chunk8 E _ F 0x18 (SLit RD_MASK2) RD_MASK2);
          [reflexivity | unfold RD_MASK2; lia | exact V18].
      * apply (pl_chunk8 E _ F 0x38 (SOff 32 0) localv);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
          | lia | exact V38].
      * apply (pl_chunk8 E _ F 0x40 (SOff 33 0) textv);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
          | lia | exact V40].
    + split; [lia|]. split; [lia|]. split; [intros oo Hoo; apply W208; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (pl_chunk8 E _ F 208 (SOff 34 0) rpv);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | lia | exact V208].
    + split; [lia|]. split; [lia|]. split; [intros oo Hoo; apply W8; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (pl_chunk8 E _ F 8 (SOff 35 0) dslot);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | lia | exact V8].
  - apply pairwise_disjoint_of_extents. unfold pl_fr_ro, pl_fr_rp, pl_fr_d, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pl_facts_B]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U8, U21, U24, U26, U27. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; try lia.
Qed.

Lemma plC_entry : forall (W : world tfibsegs) regs mem F dv dslot,
  getr regs 2 = w64 F -> getr regs 24 = w64 dv -> getr regs 8 = w64 SHADOW_OFF ->
  2 ^ 46 <= F <= 2 ^ 47 - 224 -> F mod 16 = 0 -> 0 <= dv <= 16 -> 0 <= dslot < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 8) 8 dslot ->
  (forall a, F + 8 <= a < F + 16 -> writable_at tfibsegs (mrestrict (w_H W) mem) a) ->
  st_ok tfibsegs (Ereg regs [w64 0; w64 0; w64 0; w64 dslot]) ss_C
    (restrict (w_H W) (mkst regs (Z_to_bv 64 PL_C) mem (seg_rom tfibsegs))).
Proof.
  intros W regs mem F dv dslot R2 R24 R8 HF HF16 Hdv Hds V8 W8.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs [w64 0; w64 0; w64 0; w64 dslot]).
  assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
  assert (E8 : ew E 8 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
  assert (E24 : ew E 24 = w64 dv) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (E35 : ew E 35 = w64 dslot) by (unfold E; exact (ew_Ereg_extra regs _ 3)).
  assert (U2 : bv_unsigned (ew E 2) = F) by (rewrite E2; apply unsigned_lit_small; lia).
  assert (U8 : bv_unsigned (ew E 8) = SHADOW_OFF) by (rewrite E8; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U24 : bv_unsigned (ew E 24) = dv) by (rewrite E24; apply unsigned_lit_small; lia).
  unfold ss_C. apply (entry_st_ok_full tfibsegs); change (Ereg regs [w64 0; w64 0; w64 0; w64 dslot]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold pl_fr_d, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split; [intros oo Hoo; apply W8; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (pl_chunk8 E _ F 8 (SOff 35 0) dslot);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | lia | exact V8].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pl_facts_C]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U8, U24. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; try lia.
Qed.

End e.

(* ======== the memory a callee keeps (local copies of G5's lib/A/FMW_kitS.v and G6's lib/A/FMW_kit.v, which this
   worktree does not carry) ======== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Lemma pl_word_end_le : forall x base ext, base mod 16 = 0 -> ext mod 8 = 0 -> x < base + ext ->
  x - x mod 8 + 8 <= base + ext.
Proof.
intros x base ext H1 H2 H3.
pose proof (Z.div_mod base 16 ltac:(lia)) as D1. pose proof (Z.div_mod ext 8 ltac:(lia)) as D2.
pose proof (Z.div_mod x 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D4.
lia.
Qed.

Lemma pl_extent_mod8 : forall k, 0 <= ck_req k -> ck_extent k mod 8 = 0.
Proof.
intros k Hq. unfold ck_extent. destruct (from_primary (ck_req k)) eqn:Ep.
- pose proof (primary_geometry (ck_req k) Hq Ep) as (_ & _ & _ & H32 & _).
  set (c := class_size (chunk_class (ck_req k))) in *.
  pose proof (Z.div_mod c 32 ltac:(lia)) as D. pose proof (Z.div_mod c 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as R8. lia.
- pose proof (secondary_geometry (ck_req k) Hq Ep) as (_ & _ & _ & _ & HP & _).
  set (s := sec_map_size (ck_req k)) in *. unfold kPage in *.
  pose proof (Z.div_mod s 4096 ltac:(lia)) as D. pose proof (Z.div_mod (s - 4096) 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound (s - 4096) 8 ltac:(lia)) as R8. lia.
Qed.

Lemma pl_block_tail_vis : forall ly S (W : world tfibsegs) mem md b m,
  AR tfibsegs B ly S W mem md -> In (b, m) (ablocks B ly S) -> 0 < m ->
  forall a, b <= a < (b + m - 1) - (b + m - 1) mod 8 + 8 -> aview tfibsegs (w_H W) mem a <> None.
Proof.
intros ly S W mem md b m HAR Hin Hm a Ha.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (Z_lt_le_dec a (b + m)) as [Hlt | Hge].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & Hpres & _).
  apply (aview_some_of_apresent tfibsegs). exact (proj1 (Hpres a ltac:(lia))).
- destruct HAR as (M & _).
  apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn).
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & Hb16 & Huser & _ & _ & Hreq & Hext & _).
  rewrite Hn, Hrq in Hext.
  assert (Hcn : ck_n k = m) by (unfold ck_n; rewrite Hn; exact Hrq).
  pose proof (pl_extent_mod8 k ltac:(lia)) as Hx8.
  pose proof (pl_word_end_le (b + m - 1) (ck_base B ly k) (ck_extent k) Hb16 Hx8 ltac:(lia)) as Hend.
  pose proof (am_junk B ly S _ M) as HJ. rewrite Forall_forall in HJ.
  specialize (HJ (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k)).
  unfold range_vis in HJ. cbn [fst snd] in HJ.
  assert (NSH : forall e', sptr_exp (ck_beg k) <> ASh e') by (intros e'; destruct (ck_beg k); cbn; discriminate).
  rewrite (aeval_aoff B ly (sptr_exp (ck_beg k)) (ck_rz k + ck_n k) NSH) in HJ.
  assert (Eb : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
  replace a with (aeval B ly (sptr_exp (ck_beg k)) + (ck_rz k + ck_n k) + (a - (b + m))) by lia.
  apply HJ; [|lia].
  unfold ajunk. apply in_cons. apply in_cons.
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; left.
  apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. cbv zeta.
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_eq.
Qed.

Lemma pl_shadow_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr, SHADOW_OFF in *.
assert (M1 : (2147450880 + x / 8) / 8 <= (2147450880 + x' / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1); lia).
assert (M2 : (2147450880 + (x' + n' - 1) / 8) / 8 <= (2147450880 + (x + n - 1) / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)); lia).
lia.
Qed.

Lemma pl_word_end_mono : forall x y, x <= y -> x - x mod 8 + 8 <= y - y mod 8 + 8.
Proof.
intros x y H. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.div_mod y 8 ltac:(lia)) as Dy.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)).
assert (x / 8 <= y / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma pl_cstr_ok_kept_blk : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S') -> b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  (forall a, p <= a < p + Z.of_nat (length l) + 1 -> ~ inFP FP a) ->
  cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m HJ Hin Hin' Hb Hbm HnF
  ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hm : 0 < m) by lia.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). replace a with (b + (a - b)) by lia.
  apply (F2 b m (a - b) Hin Hin'); [rewrite Hrq; lia | replace (b + (a - b)) with a by lia; apply HnF; lia]. }
split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
split.
{ apply (range_addressable_of_block tfibsegs B LAWS ly' S' W' mem' md' b m p _ HAR' Hin' Hb). rewrite Hrq. lia. }
split.
{ destruct (al_shadow _ _ LAWS ly' S' W' mem' md' b m HAR' Hin') as (_ & Hhv').
  apply (pl_shadow_hull_sub _ b (req_size m) p _ Hhv' Hb); rewrite ?Hrq; lia. }
intros a Ha. apply (pl_block_tail_vis ly' S' W' mem' md' b m HAR' Hin' Hm).
pose proof (pl_word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.

Lemma pl_cstr_ok_suffix : forall (W : world tfibsegs) mem p0 l0 k, (k <= length l0)%nat ->
  cstr_ok tfibsegs W mem p0 l0 -> cstr_ok tfibsegs W mem (p0 + Z.of_nat k) (skipn k l0).
Proof.
intros W mem p0 l0 k Hk ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
assert (Hlen : Z.of_nat (length (skipn k l0)) = Z.of_nat (length l0) - Z.of_nat k) by (rewrite length_skipn; lia).
assert (Eend : p0 + Z.of_nat k + Z.of_nat (length (skipn k l0)) = p0 + Z.of_nat (length l0)) by lia.
split; [split|].
- rewrite <- (firstn_skipn k l0) in Hg. rewrite <- app_assoc in Hg. apply (garr8_app tfibsegs) in Hg as [_ Hg].
  rewrite length_firstn in Hg. replace (Nat.min k (length l0)) with k in Hg by lia. exact Hg.
- rewrite <- (firstn_skipn k l0) in Hnz. apply Forall_app in Hnz as [_ Hnz]. exact Hnz.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
  split; [intros x Hx; apply Hra; lia|].
  split; [apply (pl_shadow_hull_sub _ p0 (Z.of_nat (length l0) + 1)); [exact Hhv | lia | lia | lia]|].
  intros a Ha. rewrite Eend in Ha. exact (Htl a Ha).
Qed.

Lemma pl_relro_img : forall a, FM_RLO <= a < FM_RHI -> in_img tfibsegs a.
Proof.
intros a Ha. unfold FM_RLO, FM_RHI in Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in
  let h := eval vm_compute in sz in change lo with l; change sz with h end. lia.
Qed.

Lemma pl_arodata_kept : forall STK sp0 ly S W0 mem0 md0 own lyc Sc W memc mdc k,
  ajournal tfibsegs B STK sp0 [] ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W0) mem0) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) memc).
Proof.
intros STK sp0 ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (inFP_nil a)
  | exact (fp_spares_closed [] a sink_closed_nil)].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
exact (pl_relro_img a Hgot).
Qed.

Lemma pl_cstr_ok_kept : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k p l,
  fm_img_facts tfibsegs B ->
  ajournal tfibsegs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') mem') ->
  cstr_kept B ly S p l -> cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k p l IMG HJ Hinc HRO' Hk Hc.
pose proof HJ as (HAR' & _).
destruct Hk as [(b & m & Hin & Hb & Hbm) | (p0 & l0 & kk & Hsrc & Hkl & -> & ->)].
- apply (pl_cstr_ok_kept_blk STK sp0 [] ly S W mem md own ly' S' W' mem' md' k p l b m HJ Hin (Hinc _ Hin) Hb Hbm);
    [intros a Ha Hf; exact (inFP_nil a Hf) | exact Hc].
- apply (pl_cstr_ok_suffix W' mem' p0 l0 kk Hkl).
  destruct Hsrc as [Hro | (ps & Hf & ->)].
  + destruct (IMG ly' S' W' mem' md' HAR' HRO') as (_ & _ & _ & HS & _).
    exact (proj1 (proj1 (Forall_forall _ _) HS (p0, l0) Hro)).
  + destruct (IMG ly' S' W' mem' md' HAR' HRO') as (_ & _ & _ & _ & HF). exact (proj1 (HF p0 ps Hf)).
Qed.

Lemma pl_cstr_kept_kept : forall ly S ly' S' p l,
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  cstr_kept B ly S p l -> cstr_kept B ly' S' p l.
Proof.
intros ly S ly' S' p l Hinc [(b & m & Hin & H1 & H2) | Himg].
- left. exists b, m. split; [exact (Hinc _ Hin) | split; assumption].
- right. exact Himg.
Qed.
(* ---- what the loop's invariant needs of the memory a step changes ---- *)
Definition pl_win (cx : rdcx) (lo a : Z) : Prop :=
  (lo <= a < cx_F cx) \/ (cx_F cx + 8 <= a < cx_F cx + 16) \/ (cx_sp cx <= a < cx_sp cx + 8).

Definition pl_rest (cx : rdcx) : list (Z * Z) :=
  [(0x18, RD_MASK2); (0x20, cx_u cx); (0x30, cx_ulen cx); (0x40, cx_t cx); (0x48, cx_u cx - 2);
   (0x50, cx_u cx - 3); (0x58, RD_PREFIX); (0x60, RD_MASK1)].
Lemma pl_loc_list : forall cx d, rd_loc_list cx d = (0, cx_sp cx) :: (8, Z.of_nat d) :: pl_rest cx.
Proof. reflexivity. Qed.

Lemma pl_saved_kept : forall cx (W W' : world tfibsegs) mem mem',
  rd_saved_ok cx W mem ->
  (forall a, cx_F cx + 104 <= a < cx_F cx + 208 -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  rd_saved_ok cx W' mem'.
Proof.
intros cx W W' mem mem' H HAV. unfold rd_saved_ok in *. rewrite Forall_forall in H |- *.
intros s Hs. specialize (H s Hs).
assert (Hoff : 104 <= fst s <= 200).
{ cbv [RD_SAVED In] in Hs. repeat (destruct Hs as [<-|Hs]; [cbn; lia|]). destruct Hs. }
apply (g3_val_mem_kept W W' mem mem'); [exact H|]. intros i Hi. cbn in Hi. apply HAV. lia.
Qed.

Lemma pl_slots_kept : forall cx (W W' : world tfibsegs) mem mem' sl,
  rd_slots_ok cx W mem sl ->
  (forall s, In s sl -> forall i, 0 <= i < 8 ->
     aview tfibsegs (w_H W') mem' (cx_F cx + fst s + i) = aview tfibsegs (w_H W) mem (cx_F cx + fst s + i)) ->
  rd_slots_ok cx W' mem' sl.
Proof.
intros cx W W' mem mem' sl H HAV. unfold rd_slots_ok in *. rewrite Forall_forall in H |- *.
intros s Hs. destruct (H s Hs) as [Hv Hb]. split; [|exact Hb].
apply (g3_val_mem_kept W W' mem mem'); [exact Hv|]. intros i Hi. cbn in Hi. apply HAV; [exact Hs | lia].
Qed.

Definition PL_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18]%bv.
Definition pl_regs_same (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18.

Lemma pl_regs_same_of_kept : forall (regs regs' : bvmap 5 word),
  (forall r, In r PL_KEPT -> getr regs' r = getr regs r) -> pl_regs_same regs regs'.
Proof.
intros regs regs' H. unfold pl_regs_same.
split; [apply H; cbv [PL_KEPT In]; left; reflexivity|].
split; [apply H; cbv [PL_KEPT In]; right; left; reflexivity|].
split; [apply H; cbv [PL_KEPT In]; right; right; left; reflexivity|].
split; [apply H; cbv [PL_KEPT In]; right; right; right; left; reflexivity|].
split; [apply H; cbv [PL_KEPT In]; right; right; right; right; left; reflexivity
       |apply H; cbv [PL_KEPT In]; right; right; right; right; right; left; reflexivity].
Qed.

Lemma pl_keepr : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' -> pl_regs_same regs regs'.
Proof.
intros regs regs' HP. unfold pl_regs_same.
split; [exact (HP 2 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 3 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 4 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 8 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 9 ltac:(unfold acallee_saved; lia)) | exact (HP 18 ltac:(unfold acallee_saved; lia))].
Qed.

Lemma pl_com_kept : forall cx k ly3 S3 (W3 : world tfibsegs) regs3 mem3 md3 regsB memB mdB lo,
  rd_com B cx k [] ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 memB mdB k ->
  alloc_ceiling <= lo -> lo <= cx_F cx -> alloc_ceiling + 4096 <= cx_F cx -> cx_sp cx + 16 <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pl_win cx lo a -> aview tfibsegs (w_H W3) memB a = aview tfibsegs (w_H W3) mem3 a) ->
  pl_regs_same regs3 regsB ->
  rd_com B cx k [] ly3 S3 W3 regsB memB mdB.
Proof.
intros cx k ly3 S3 W3 regs3 mem3 md3 regsB memB mdB lo HCOM HJ Hlo HloF HFlo HFhi HAV HP.
pose proof HCOM as (HJ0 & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof asan_consts as (CC & _).
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (KL : g3_low_kept W3 W3 mem3 memB).
{ intros a Ha. apply HAV; [lia|]. unfold pl_win. lia. }
split; [change (unpoison [] memB) with memB; exact HJ|]. split; [exact Hk|].
destruct HP as (Q2 & Q3 & Q4 & Q8 & _).
split; [rewrite Q2; exact R2|].
split; [rewrite Q3; exact R3|].
split; [rewrite Q4; exact R4|].
split; [rewrite Q8; exact R8|].
split.
{ apply (pl_saved_kept cx W3 W3 mem3 memB HSV). intros a Ha. apply HAV; [lia|]. unfold pl_win. lia. }
split.
{ intros a Ha. rewrite (HAV a ltac:(lia) ltac:(unfold pl_win; lia)). exact (K16 a Ha). }
split; [exact (g3_arodata_kept B W3 W3 mem3 memB HRO KL)|].
split; [exact (g3_cstr_ok_kept W3 W3 mem3 memB _ _ Ct KL)|].
split; [exact (g3_cstr_ok_kept W3 W3 mem3 memB _ _ Cu KL)|].
split; [exact Kt | exact Ku].
Qed.

(* the loop's invariant with *rp read off (rd_loop is the case rpv = v + d) *)
Definition pl_mid (cx : rdcx) (d : nat) (rpv : Z) ly3 S3 (W3 : world tfibsegs) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model) : Prop :=
  rd_com B cx EV_names [] ly3 S3 W3 regs3 mem3 md3 /\
  getr regs3 9 = w64 32 /\ getr regs3 18 = w64 5 /\
  rd_slots_ok cx W3 mem3 (rd_loc_list cx d) /\
  val_mem tfibsegs (mrestrict (w_H W3) mem3) (cx_sp cx) 8 rpv /\
  Permutation (ablocks B ly3 S3) (ablocks B (cx_ly cx) (cx_S cx)) /\
  fm_glob tfibsegs W3 mem3 (cx_live cx) (Z.max (cx_peak cx) (cx_live cx + cx_ulen cx + 3)) (cx_cnt cx + 1)
    (cx_fail cx) /\
  cx_cnt cx <> cx_fail cx /\ cx_ub cx <> [] /\ whole (cx_tb cx) (cx_ub cx) = false /\ (d <= 16)%nat.

Lemma pl_mid_of_loop : forall cx d ly3 S3 W3 regs3 mem3 md3,
  rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 -> pl_mid cx d (cx_v cx + Z.of_nat d) ly3 S3 W3 regs3 mem3 md3.
Proof. intros cx d ly3 S3 W3 regs3 mem3 md3 H. exact H. Qed.
Lemma pl_loop_of_mid : forall cx d ly3 S3 W3 regs3 mem3 md3,
  pl_mid cx d (cx_v cx + Z.of_nat d) ly3 S3 W3 regs3 mem3 md3 -> rd_loop B cx d ly3 S3 W3 regs3 mem3 md3.
Proof. intros cx d ly3 S3 W3 regs3 mem3 md3 H. exact H. Qed.

Lemma pl_mid_kept : forall cx d d' rpv rpv' ly3 S3 (W3 : world tfibsegs) regs3 mem3 md3 regsB memB mdB lo,
  pl_mid cx d rpv ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 memB mdB EV_names ->
  alloc_ceiling <= lo -> lo <= cx_F cx -> alloc_ceiling + 4096 <= cx_F cx -> cx_sp cx + 16 <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pl_win cx lo a -> aview tfibsegs (w_H W3) memB a = aview tfibsegs (w_H W3) mem3 a) ->
  pl_regs_same regs3 regsB ->
  val_mem tfibsegs (mrestrict (w_H W3) memB) (cx_sp cx) 8 rpv' ->
  val_mem tfibsegs (mrestrict (w_H W3) memB) (cx_F cx + 8) 8 (Z.of_nat d') -> (d' <= 16)%nat ->
  pl_mid cx d' rpv' ly3 S3 W3 regsB memB mdB.
Proof.
intros cx d d' rpv rpv' ly3 S3 W3 regs3 mem3 md3 regsB memB mdB lo HMID HJ Hlo HloF HFlo HFhi HAV HP Hrp Hd8 Hd'.
pose proof HMID as (HCOM & R9 & R18 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof asan_consts as (CC & _).
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (KL : g3_low_kept W3 W3 mem3 memB).
{ intros a Ha. apply HAV; [lia|]. unfold pl_win. lia. }
pose proof HP as (_ & _ & _ & _ & Q9 & Q18).
split; [exact (pl_com_kept cx EV_names ly3 S3 W3 regs3 mem3 md3 regsB memB mdB lo HCOM HJ Hlo HloF HFlo HFhi HAV HP)|].
split; [rewrite Q9; exact R9|].
split; [rewrite Q18; exact R18|].
split.
{ rewrite pl_loc_list in HSLOTS |- *. unfold rd_slots_ok in HSLOTS |- *.
  apply Forall_cons_iff in HSLOTS as [H0 HSLOTS]. apply Forall_cons_iff in HSLOTS as [_ Hrest].
  apply Forall_cons.
  { cbn [fst snd] in H0 |- *. destruct H0 as [Hv Hb]. split; [|exact Hb].
    apply (g3_val_mem_kept W3 W3 mem3 memB); [exact Hv|].
    intros i Hi. cbn in Hi. apply HAV; [lia|]. unfold pl_win. lia. }
  apply Forall_cons.
  { cbn [fst snd]. split; [exact Hd8 | lia]. }
  apply (pl_slots_kept cx W3 W3 mem3 memB (pl_rest cx) Hrest).
  intros s Hs i Hi.
  assert (Hoff : 24 <= fst s <= 96)
    by (cbv [pl_rest In] in Hs; repeat (destruct Hs as [<-|Hs]; [cbn; lia|]); destruct Hs).
  apply HAV; [lia|]. unfold pl_win. lia. }
split; [exact Hrp|]. split; [exact HPERM|].
split; [exact (g3_fm_glob_kept W3 W3 mem3 memB _ _ _ _ HGL KL)|].
split; [exact Hcf|]. split; [exact Hub|]. split; [exact Hwh | exact Hd'].
Qed.

Definition pl_same (cx : rdcx) (W : world tfibsegs) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ pl_win cx (cx_F cx) a ->
    aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.
Lemma pl_same_trans : forall cx W m m' m'', pl_same cx W m m' -> pl_same cx W m' m'' -> pl_same cx W m m''.
Proof. intros cx W m m' m'' H1 H2 a Ha Hn. rewrite (H2 a Ha Hn). exact (H1 a Ha Hn). Qed.

(* ---- the cut invariant rd_PL across a step that writes only the frame slots ---- *)
Definition PL_KEPT2 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 26; 27]%bv.
Definition pl_regs_pl (regs regs' : bvmap 5 word) : Prop :=
  pl_regs_same regs regs' /\
  getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\
  getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\
  getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26.

Ltac pl_in := cbv [PL_KEPT PL_KEPT2 In]; repeat (first [left; reflexivity | right]).

Lemma pl_regs_pl_of_pres : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' -> pl_regs_pl regs regs'.
Proof.
intros regs regs' HP. split; [exact (pl_keepr regs regs' HP)|].
split; [exact (HP 19 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 20 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 21 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 22 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 23 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 24 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 25 ltac:(unfold acallee_saved; lia)) | exact (HP 26 ltac:(unfold acallee_saved; lia))].
Qed.

Lemma pl_regs_pl_of_kept : forall (regs regs' : bvmap 5 word),
  (forall r, In r PL_KEPT2 -> getr regs' r = getr regs r) ->
  getr regs' 20 = getr regs 20 -> getr regs' 25 = getr regs 25 -> pl_regs_pl regs regs'.
Proof.
intros regs regs' H H20 H25.
assert (K : forall r, In r PL_KEPT -> getr regs' r = getr regs r).
{ intros r Hr. apply H. cbv [PL_KEPT PL_KEPT2 In] in Hr |- *. tauto. }
split; [exact (pl_regs_same_of_kept regs regs' K)|].
split; [apply H; pl_in|]. split; [exact H20|]. split; [apply H; pl_in|].
split; [apply H; pl_in|]. split; [apply H; pl_in|]. split; [apply H; pl_in|].
split; [exact H25 | apply H; pl_in].
Qed.

Lemma pl_PL_kept : forall cx i d f s11 p1 p2 p3 o q ly3 S3 (W3 : world tfibsegs) regs3 mem3 md3 regsB memB mdB lo,
  rd_PL B cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 memB mdB EV_names ->
  alloc_ceiling <= lo -> lo <= cx_F cx -> alloc_ceiling + 4096 <= cx_F cx -> cx_sp cx + 16 <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pl_win cx lo a -> aview tfibsegs (w_H W3) memB a = aview tfibsegs (w_H W3) mem3 a) ->
  pl_regs_pl regs3 regsB ->
  val_mem tfibsegs (mrestrict (w_H W3) memB) (cx_sp cx) 8 (cx_v cx + Z.of_nat d) ->
  val_mem tfibsegs (mrestrict (w_H W3) memB) (cx_F cx + 8) 8 (Z.of_nat d) ->
  rd_PL B cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regsB memB mdB.
Proof.
intros cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 regsB memB mdB lo HPL HJ Hlo HloF HFlo HFhi HAV HP Hrp Hd8.
pose proof asan_consts as (CC & _).
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
unfold rd_PL in HPL |- *. cbv zeta in HPL |- *.
destruct HPL as (HLOOP & HACC & Hilt & HDECL & HFI & Ho & HFirst & HLast & Hqn & HPlainq & HS38 & R19 & R20 & R21 &
  R22 & R23 & R24 & R25 & R26).
pose proof HP as (HPS & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26).
pose proof (pl_mid_of_loop cx d ly3 S3 W3 regs3 mem3 md3 HLOOP) as HMID.
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdle).
split.
{ apply pl_loop_of_mid.
  exact (pl_mid_kept cx d d (cx_v cx + Z.of_nat d) (cx_v cx + Z.of_nat d) ly3 S3 W3 regs3 mem3 md3 regsB memB mdB lo
    HMID HJ Hlo HloF HFlo HFhi HAV HPS Hrp Hd8 Hdle). }
split; [exact HACC|]. split; [exact Hilt|]. split; [exact HDECL|]. split; [exact HFI|]. split; [exact Ho|].
split; [exact HFirst|]. split; [exact HLast|]. split; [exact Hqn|]. split; [exact HPlainq|].
split.
{ apply (pl_slots_kept cx W3 W3 mem3 memB _ HS38). intros ss Hss j Hj. cbn in Hj.
  cbv [In] in Hss. destruct Hss as [<-|[]]. cbn [fst]. apply HAV; [lia | unfold pl_win; lia]. }
split; [rewrite Q19; exact R19|]. split; [rewrite Q20; exact R20|]. split; [rewrite Q21; exact R21|].
split; [rewrite Q22; exact R22|]. split; [rewrite Q23; exact R23|]. split; [rewrite Q24; exact R24|].
split; [rewrite Q25; exact R25 | rewrite Q26; exact R26].
Qed.

Definition PL_KEPT4 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 26]%bv.
Ltac pl_in4 := cbv [PL_KEPT4 In]; repeat (first [left; reflexivity | right]).
Lemma pl_regs_pl_of_kept4 : forall (regs regs' : bvmap 5 word),
  (forall r, In r PL_KEPT4 -> getr regs' r = getr regs r) ->
  getr regs' 20 = getr regs 20 -> getr regs' 25 = getr regs 25 -> pl_regs_pl regs regs'.
Proof.
intros regs regs' H H20 H25.
split; [apply pl_regs_same_of_kept; intros r Hr; apply H; cbv [PL_KEPT PL_KEPT4 In] in Hr |- *; tauto|].
split; [apply H; pl_in4|]. split; [exact H20|]. split; [apply H; pl_in4|].
split; [apply H; pl_in4|]. split; [apply H; pl_in4|]. split; [apply H; pl_in4|].
split; [exact H25 | apply H; pl_in4].
Qed.
Lemma pl_regs_pl_trans : forall (r1 r2 r3 : bvmap 5 word), pl_regs_pl r1 r2 -> pl_regs_pl r2 r3 -> pl_regs_pl r1 r3.
Proof.
intros r1 r2 r3 (H1 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26) (H2 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26).
destruct H1 as (C2 & C3 & C4 & C8 & C9 & C18). destruct H2 as (D2 & D3 & D4 & D8 & D9 & D18).
split; [repeat split; congruence|]. repeat split; congruence.
Qed.

(* ---- the loop's state across the call to has_prefixed ---- *)
Lemma pl_mid_hp : forall cx d rpv ly3 S3 (W3 : world tfibsegs) regs3 mem3 md3 ly5 S5 W5 regs5 mem5 md5,
  fm_img_facts tfibsegs B ->
  pl_mid cx d rpv ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_has_prefixed (cx_F cx) [] ly3 S3 W3 mem3 md3 [] ly5 S5 W5 mem5 md5 0 ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly5 S5 W5 mem5 md5 EV_names ->
  ablocks B ly5 S5 = ablocks B ly3 S3 ->
  pl_regs_same regs3 regs5 ->
  fm_glob tfibsegs W5 mem5 (cx_live cx) (Z.max (cx_peak cx) (cx_live cx + cx_ulen cx + 3)) (cx_cnt cx + 1)
    (cx_fail cx) ->
  alloc_ceiling + 4096 <= cx_F cx -> cx_sp cx + 16 <= 2 ^ 47 ->
  pl_mid cx d rpv ly5 S5 W5 regs5 mem5 md5.
Proof.
intros cx d rpv ly3 S3 W3 regs3 mem3 md3 ly5 S5 W5 regs5 mem5 md5 HIMG HMID HJhp HJ Hablk HPS HGL5 HFlo HFhi.
pose proof asan_consts as (CC & _).
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (FHP : STK_has_prefixed = 8304) by reflexivity.
pose proof HMID as (HCOM & R9 & R18 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof HCOM as (HJ0 & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HJhp as (_ & _ & _ & _ & _ & _ & _ & _ & HAVh & _).
pose proof HPS as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18).
assert (Hinc : forall x, In x (ablocks B ly3 S3) -> In x (ablocks B ly5 S5)) by (rewrite Hablk; tauto).
assert (HRO5 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W5) mem5))
  by exact (pl_arodata_kept STK_has_prefixed (cx_F cx) ly3 S3 W3 mem3 md3 [] ly5 S5 W5 mem5 md5 0 HJhp HRO).
assert (HCOM5 : rd_com B cx EV_names [] ly5 S5 W5 regs5 mem5 md5).
{ split; [change (unpoison [] mem5) with mem5; exact HJ|]. split; [exact Hk|].
  split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|].
  split; [rewrite Q4; exact R4|]. split; [rewrite Q8; exact R8|].
  split.
  { apply (pl_saved_kept cx W3 W5 mem3 mem5 HSV). intros a Ha. apply HAVh; lia. }
  split.
  { intros a Ha. rewrite (HAVh a ltac:(lia) ltac:(lia)). exact (K16 a Ha). }
  split; [exact HRO5|].
  split; [exact (pl_cstr_ok_kept STK_has_prefixed (cx_F cx) ly3 S3 W3 mem3 md3 [] ly5 S5 W5 mem5 md5 0
    (cx_t cx) (cx_tb cx) HIMG HJhp Hinc HRO5 Kt Ct)|].
  split; [exact (pl_cstr_ok_kept STK_has_prefixed (cx_F cx) ly3 S3 W3 mem3 md3 [] ly5 S5 W5 mem5 md5 0
    (cx_u cx) (cx_ub cx) HIMG HJhp Hinc HRO5 Ku Cu)|].
  split; [exact (pl_cstr_kept_kept ly3 S3 ly5 S5 _ _ Hinc Kt)
         |exact (pl_cstr_kept_kept ly3 S3 ly5 S5 _ _ Hinc Ku)]. }
split; [exact HCOM5|].
split; [rewrite Q9; exact R9|]. split; [rewrite Q18; exact R18|].
split.
{ apply (pl_slots_kept cx W3 W5 mem3 mem5 _ HSLOTS). intros ss Hss j Hj.
  cbn in Hj.
  assert (Hoff : 0 <= fst ss <= 96).
  { rewrite pl_loc_list in Hss. cbv [pl_rest In] in Hss.
    repeat (destruct Hss as [<-|Hss]; [cbn; lia|]). destruct Hss. }
  apply HAVh; lia. }
split.
{ apply (g3_val_mem_kept W3 W5 mem3 mem5); [exact HRP|]. intros j Hj. cbn in Hj. apply HAVh; lia. }
split; [rewrite Hablk; exact HPERM|].
split; [exact HGL5|]. split; [exact Hcf|]. split; [exact Hub|]. split; [exact Hwh | exact Hdle].
Qed.

(* ======== the walk ======== *)
Variable CTX : list (list Z).
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis ISALNUM : aisalnum_realizes tfibsegs B PC_isalnum.
Hypothesis HASP : has_prefixed_spec tfibsegs B.

(* 0x82070, after has_prefixed: *rp already carries the extra reading *)
Definition pl_atC (cx : rdcx) (i d f s11 p1 p2 p3 o : nat) ly4 S4 (W4 : world tfibsegs) regs4 mem4 md4 : Prop :=
  pl_mid cx d (cx_v cx + Z.of_nat d + 1) ly4 S4 W4 regs4 mem4 md4 /\
  rd_acc cx i d f /\ (i < length (cx_tb cx))%nat /\ rd_decl cx i s11 p1 p2 p3 /\
  find_idx (fun c => c =? 62) (skipn (S p3) (cx_tb cx)) = Some o /\ (o < length (cx_ub cx))%nat /\
  firstn o (skipn (S p3) (cx_tb cx)) = firstn o (cx_ub cx) /\
  last (skipn o (cx_ub cx)) 0 <> 46 /\ forallb plain_ok (skipn o (cx_ub cx)) = true /\ (d < 16)%nat /\
  getr regs4 19 = w64 (cx_t cx + Z.of_nat (S p3) + Z.of_nat o) /\ getr regs4 21 = w64 1 /\
  getr regs4 24 = w64 (Z.of_nat d).

Ltac pl_awr HU :=
  lazymatch goal with
  | |- awr_ok ?sg ?BB ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg BB E rs' stk sp0 fp b0 bc ly own)
  | |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := (-224));
      [ reflexivity
      | cbn [YP09.r_base base_val ew ewset Nat.eqb]; rewrite HU; lia
      | cbn [YP09.r_wlo]; lia
      | cbn [YP09.r_whi]; lia
      | ] ].

Lemma pl_from_C : forall f cx i d s11 p1 p2 p3 o ly4 S4 W4 regs4 mem4 md4 res,
  rd_seg_L B CTX f -> rd_base B CTX cx ->
  pl_atC cx i d (S f) s11 p1 p2 p3 o ly4 S4 W4 regs4 mem4 md4 ->
  getr regs4 10 = w64 res ->
  res = (if token (cx_tb cx) (firstn (p2 - p1) (skipn p1 (cx_tb cx))) (skipn o (cx_ub cx)) then 1 else 0) ->
  SRr tfibsegs W4 (cfg_at tfibsegs PL_C regs4 mem4 md4) (rd_post B cx).
Proof.
intros f cx i d s11 p1 p2 p3 o ly4 S4 W4 regs4 mem4 md4 res HSEGL HB HC R10 Hres.
pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs. pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (CC & _).
destruct HC as (HMID & HACC & Hilt & HDECL & HFI & Ho & HFirst & HLast & HPlain & Hd16 & R19 & R21 & R24).
pose proof HMID as (HCOM & R9 & R18 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof HCOM as (HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HB as (HAN & _ & _ & _ & _ & _ & _ & Htopr & _).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & _).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (HSP : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (HFlo : alloc_ceiling + 4096 <= cx_F cx) by lia.
assert (HFhi : cx_sp cx + 16 <= 2 ^ 47) by lia.
assert (HF16 : cx_F cx mod 16 = 0)
  by (rewrite HFsp; replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia; rewrite Z_mod_plus_full;
      rewrite HSP; exact Hal16).
assert (V8 : val_mem tfibsegs (mrestrict (w_H W4) mem4) (cx_F cx + 8) 8 (Z.of_nat d)).
{ unfold rd_slots_ok in HSLOTS. rewrite Forall_forall in HSLOTS.
  destruct (HSLOTS (8, Z.of_nat d) ltac:(rewrite pl_loc_list; cbn; tauto)) as [Hv _]. exact Hv. }
assert (W8 : forall a, cx_F cx + 8 <= a < cx_F cx + 16 -> writable_at tfibsegs (mrestrict (w_H W4) mem4) a).
{ intros a Ha. apply (apresent_writable tfibsegs). apply Hpresj. lia. }
pose proof (plC_entry W4 regs4 mem4 (cx_F cx) (Z.of_nat d) (Z.of_nat d) R2 R24 R8
  ltac:(lia) HF16 ltac:(lia) ltac:(lia) V8 W8) as HS.
set (E := Ereg regs4 [w64 0; w64 0; w64 0; w64 (Z.of_nat d)]) in *.
assert (E10 : ew E 10 = w64 res) by (unfold E; rewrite (ew_Ereg_nat regs4 _ 10 10%bv eq_refl); exact R10).
assert (E19 : ew E 19 = w64 (cx_t cx + Z.of_nat (S p3) + Z.of_nat o))
  by (unfold E; rewrite (ew_Ereg_nat regs4 _ 19 19%bv eq_refl); exact R19).
assert (E21 : ew E 21 = w64 1) by (unfold E; rewrite (ew_Ereg_nat regs4 _ 21 21%bv eq_refl); exact R21).
assert (E24 : ew E 24 = w64 (Z.of_nat d)) by (unfold E; rewrite (ew_Ereg_nat regs4 _ 24 24%bv eq_refl); exact R24).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
  by (unfold E; rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E2a : ew E 2 = getr regs4 2) by (unfold E; exact (ew_Ereg_nat regs4 _ 2 2%bv eq_refl)).
assert (Hclose : (S p3 + o < length (cx_tb cx))%nat).
{ pose proof (pl_find_idx_lt _ _ _ HFI) as Hlt. rewrite length_skipn in Hlt. lia. }
pose proof Ct as ((_ & _) & Ht1 & Ht2 & _).
assert (Htbnd : 0 <= cx_t cx + Z.of_nat (S p3) + Z.of_nat o + 1 < 2 ^ 64) by lia.
assert (SHOK : sh_ok tfibsegs PL_Bx [] E
  (mrestrict (w_H W4) (ms_mem (mkst regs4 (Z_to_bv 64 PL_C) mem4 (seg_rom tfibsegs))))) by constructor.
assert (Hne : skipn o (cx_ub cx) <> [])
  by (intros Hnil; apply (f_equal (@length Z)) in Hnil; rewrite length_skipn in Hnil; cbn in Hnil; lia).
assert (Hmatch : matches (cx_tb cx) (cx_ub cx) (S p3) o = true).
{ rewrite (pl_matches _ _ _ _ Ho HFirst), (pl_plain_name _ Hne HLast). exact HPlain. }
unfold rd_decl in HDECL. cbv zeta in HDECL.
destruct HDECL as (Hhead & Hs11 & Hsp & Hp1 & Hp2 & Hc58 & Hp3 & Hc60 & Hlen3).
assert (Hdecl : decl (cx_tb cx) i = DFound p1 (p2 - p1) (S p3) o (S p3 + o))
  by exact (pl_decl_found (cx_tb cx) i s11 p1 p2 p3 o Hhead Hsp Hp1 Hp2 Hc58 Hp3 Hc60 HFI).
assert (Hub0 : (length (cx_ub cx) =? 0)%nat = false) by (destruct (cx_ub cx); [congruence | reflexivity]).
assert (Hcf0 : (cx_cnt cx =? cx_fail cx) = false) by (apply Z.eqb_neq; exact Hcf).
change (unpoison [] mem4) with mem4 in HJ.
unfold cfg_at. change (w64 PL_C) with (Z_to_bv 64 PL_C).
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 PL_C) mem4 (seg_rom tfibsegs))) in HJ.
srr_branch_tok rd_tbl_ok HS SHOK PL_Bspan.
{ (* has_prefixed answered non-zero: the name is a token, readings returns 1 *)
  rewrite branch_ne_U, (U_atom E 10 res E10) in Hc by (subst res; destruct (token _ _ _); lia).
  rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  assert (Htok : token (cx_tb cx) (firstn (p2 - p1) (skipn p1 (cx_tb cx))) (skipn o (cx_ub cx)) = true)
    by (destruct (token (cx_tb cx) (firstn (p2 - p1) (skipn p1 (cx_tb cx))) (skipn o (cx_ub cx)));
        [reflexivity | exfalso; apply Hc; exact Hres]).
  destruct (pl_sc_tok (cx_tb cx) (cx_ub cx) i d f p1 (p2 - p1) (S p3) o (S p3 + o) Hilt Hdecl Hmatch Hd16 Htok)
    as [Hscan Hread].
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan RD_R; [pl_awr U2|].
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx + 8 <= a < cx_F cx + 16) ->
    aview tfibsegs (w_H W4) (ms_mem ms) a = aview tfibsegs (w_H W4) mem4 a).
  { intros a Ha Hn. apply (g3_aview_frame E (ss_mem ss_C) (w_H W4) mem4 (ms_mem ms) HFr a Ha).
    intros (r & Hin & Hr). cbn [ss_C ss_mem In] in Hin. destruct Hin as [<-|[]].
    cbn [pl_fr_d YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U2 in Hr. apply Hn. lia. }
  assert (KEw : forall a, 0 <= a < 2 ^ 64 -> ~ pl_win cx (cx_F cx) a ->
    aview tfibsegs (w_H W4) (ms_mem ms) a = aview tfibsegs (w_H W4) mem4 a)
    by (intros a Ha Hn; apply KE; [lia | unfold pl_win in Hn; lia]).
  assert (KL : g3_low_kept W4 W4 mem4 (ms_mem ms)) by (intros a Ha; apply KE; lia).
  pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs4 [w64 0; w64 0; w64 0; w64 (Z.of_nat d)] PL_KEPT HS
    ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  assert (HPR : pl_regs_same regs4 (ms_regs ms)) by exact (pl_regs_same_of_kept regs4 (ms_regs ms) KR).
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  eapply (rd_ret_holds B CTX cx EV_names ly4 S4 W4 (ms_regs ms) (ms_mem ms) _ 1 HB).
  - exact (pl_com_kept cx EV_names ly4 S4 W4 regs4 mem4 _ (ms_regs ms) (ms_mem ms) _ (cx_F cx)
      HCOM HJ ltac:(lia) ltac:(lia) HFlo HFhi KEw HPR).
  - rreg HS (21%bv : bv 5) Q21. rewrite Q21. exact E21.
  - lia.
  - split; [exact HPERM|]. split.
    + right. right. split; [exact Hub|]. split; [exact Hcf|]. split.
      * destruct HACC as (_ & _ & Hnames & _). symmetry. rewrite Hnames. exact Hscan.
      * exact (g3_fm_glob_kept W4 W4 mem4 (ms_mem ms) _ _ _ _ HGL KL).
    + rewrite Hub0, Hcf0. cbn [orb].
      destruct HACC as (_ & _ & _ & Hnr). rewrite Hnr, Hread.
      apply (g3_val_mem_kept W4 W4 mem4 (ms_mem ms)); [replace (cx_v cx + Z.of_nat (d + 1)) with
        (cx_v cx + Z.of_nat d + 1) by lia; exact HRP|].
      intros j Hj. cbn in Hj. apply KE; lia. }
{ (* has_prefixed answered zero: one more reading, back to the scan at S close with S d *)
  rewrite branch_ne_U, (U_atom E 10 res E10) in Hc by (subst res; destruct (token _ _ _); lia).
  rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  assert (Htok : token (cx_tb cx) (firstn (p2 - p1) (skipn p1 (cx_tb cx))) (skipn o (cx_ub cx)) = false)
    by (destruct (token (cx_tb cx) (firstn (p2 - p1) (skipn p1 (cx_tb cx))) (skipn o (cx_ub cx)));
        [exfalso; rewrite Hres in Hc; discriminate | reflexivity]).
  destruct (pl_sc_next (cx_tb cx) (cx_ub cx) i d f p1 (p2 - p1) (S p3) o (S p3 + o) Hilt Hdecl Hmatch Hd16 Htok)
    as [Hscan Hread].
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan RD_L; [pl_awr U2|].
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx + 8 <= a < cx_F cx + 16) ->
    aview tfibsegs (w_H W4) (ms_mem ms) a = aview tfibsegs (w_H W4) mem4 a).
  { intros a Ha Hn. apply (g3_aview_frame E (ss_mem ss_C) (w_H W4) mem4 (ms_mem ms) HFr a Ha).
    intros (r & Hin & Hr). cbn [ss_C ss_mem In] in Hin. destruct Hin as [<-|[]].
    cbn [pl_fr_d YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U2 in Hr. apply Hn. lia. }
  assert (KEw : forall a, 0 <= a < 2 ^ 64 -> ~ pl_win cx (cx_F cx) a ->
    aview tfibsegs (w_H W4) (ms_mem ms) a = aview tfibsegs (w_H W4) mem4 a)
    by (intros a Ha Hn; apply KE; [lia | unfold pl_win in Hn; lia]).
  pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs4 [w64 0; w64 0; w64 0; w64 (Z.of_nat d)] PL_KEPT HS
    ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  assert (HPR : pl_regs_same regs4 (ms_regs ms)) by exact (pl_regs_same_of_kept regs4 (ms_regs ms) KR).
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 0 r HS ltac:(vm_compute; reflexivity)) as HR0;
    cbn [ms_mem restrict] in HR0 end.
  assert (V8' : val_mem tfibsegs (mrestrict (w_H W4) (ms_mem ms)) (cx_F cx + 8) 8 (Z.of_nat (S d))).
  { apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 8 8%N (SOff 24 1) (Z.of_nat (S d)) HR0
      ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E24, unsigned_lit_small by lia; unfold w64; f_equal; lia)
      ltac:(cbn; lia) ltac:(cbn; lia)). }
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  eapply (HSEGL cx (S (S p3 + o)) (S d) ly4 S4 W4 (ms_regs ms) (ms_mem ms) _ HB).
  split; [|split; [|split]].
  - apply pl_loop_of_mid.
    apply (pl_mid_kept cx d (S d) (cx_v cx + Z.of_nat d + 1) (cx_v cx + Z.of_nat (S d))
      ly4 S4 W4 regs4 mem4 _ (ms_regs ms) (ms_mem ms) _ (cx_F cx) HMID HJ ltac:(lia) ltac:(lia) HFlo HFhi
      KEw HPR).
    + apply (g3_val_mem_kept W4 W4 mem4 (ms_mem ms));
        [replace (cx_v cx + Z.of_nat (S d)) with (cx_v cx + Z.of_nat d + 1) by lia; exact HRP|].
      intros j Hj. cbn in Hj. apply KE; lia.
    + exact V8'.
    + lia.
  - destruct HACC as (Hi1 & Hi2 & Hi3 & Hi4).
    split; [lia|]. split; [lia|]. split; [rewrite Hi3; exact Hscan|]. rewrite Hi4, Hread. lia.
  - rreg HS (20%bv : bv 5) Q20. rewrite Q20. reflexivity.
  - rreg HS (24%bv : bv 5) Q24. rewrite Q24. cbn [sv_denot ew ewset Nat.eqb].
    rewrite E19, unsigned_lit_small by lia. unfold w64. f_equal. lia. }
Qed.

Lemma pl_from_N : forall f cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3,
  rd_seg_L B CTX f -> rd_base B CTX cx ->
  rd_PL B cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 ->
  getr regs3 27 = w64 (byte_at (cx_ub cx) (o + q)) ->
  plain_ok (byte_at (cx_ub cx) (o + q)) = false ->
  SRr tfibsegs W3 (cfg_at tfibsegs PL_N regs3 mem3 md3) (rd_post B cx).
Proof.
intros f cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 HSEGL HB HPL R27 Hnp.
pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs. pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (CC & _).
unfold rd_PL in HPL. cbv zeta in HPL.
destruct HPL as (HLOOP & HACC & Hilt & HDECL & HFI & Ho & HFirst & HLast & Hqn & HPlainq & HS38 & R19 & R20 &
  R21 & R22 & R23 & R24 & R25 & R26).
pose proof HLOOP as HMID.
pose proof HMID as (HCOM & R9 & R18 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof HCOM as (HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HB as (HAN & HCTX & HROb & H10b & H11b & H12b & Hpresb & Htopr & Hvb & Hv63 & Ctb & Cub & Ktb & Kub &
  Hub255 & Htbmax & HGb & Hlv & Hcntb & Hevb & Hlbb).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARj & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (HSP : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (HFlo : alloc_ceiling + 4096 <= cx_F cx) by lia.
assert (HFhi : cx_sp cx + 16 <= 2 ^ 47) by lia.
assert (HF16 : cx_F cx mod 16 = 0) by
  (rewrite HFsp; replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia; rewrite Z_mod_plus_full;
   rewrite HSP; exact Hal16).
pose proof Ct as ((_ & _) & Ht1 & Ht2 & _).
pose proof Cu as ((HGu & HNZu) & Hu1 & Hu2 & _).
assert (Hclose : (S p3 + o < length (cx_tb cx))%nat) by
  (pose proof (pl_find_idx_lt _ _ _ HFI) as Hlt; rewrite length_skipn in Hlt; lia).
assert (Hoq : (o + q < length (cx_ub cx))%nat) by lia.
unfold rd_slots_ok in HSLOTS. rewrite pl_loc_list in HSLOTS.
apply Forall_cons_iff in HSLOTS as [SL0 HSLOTS]. apply Forall_cons_iff in HSLOTS as [SL8 HSLOTS].
cbv [pl_rest] in HSLOTS.
apply Forall_cons_iff in HSLOTS as [SL18 HSLOTS]. apply Forall_cons_iff in HSLOTS as [SL20 HSLOTS].
apply Forall_cons_iff in HSLOTS as [SL30 HSLOTS]. apply Forall_cons_iff in HSLOTS as [SL40 HSLOTS].
cbn [fst snd] in SL0, SL8, SL18, SL20, SL30, SL40.
pose proof HS38 as HS38'.
unfold rd_slots_ok in HS38'. apply Forall_cons_iff in HS38' as [SL38 _]. cbn [fst snd] in SL38.
destruct (HGu (o + q)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
rewrite app_nth1 in Vc, Rc by lia.
pose proof (plB_entry W3 PL_N regs3 mem3 (cx_F cx) (cx_u cx + Z.of_nat o + Z.of_nat q)
  (byte_at (cx_ub cx) (o + q)) (bv_unsigned (getr regs3 10)) (Z.of_nat d)
  (Z.of_nat (length (cx_ub cx) - o) - Z.of_nat q)
  (cx_u cx + Z.of_nat o) (cx_t cx) (cx_v cx + Z.of_nat d) (Z.of_nat d)
  R2 R8 ltac:(rewrite R20; unfold w64; f_equal; lia) R21 R25 R24 R26 R27
  ltac:(unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity)
  ltac:(lia) HF16 ltac:(lia) ltac:(unfold byte_at; lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  (proj1 SL18) (proj1 SL38) (proj1 SL40)
  ltac:(replace (cx_F cx + 208) with (cx_sp cx) by lia; exact HRP) (proj1 SL8)
  ltac:(intros a Ha; apply (apresent_writable tfibsegs); apply Hpresj; lia)
  ltac:(intros a Ha; apply (apresent_writable tfibsegs); apply Hpresj; lia)) as HS.
set (E := Ereg regs3 [w64 (cx_u cx + Z.of_nat o); w64 (cx_t cx); w64 (cx_v cx + Z.of_nat d);
  w64 (Z.of_nat d)]) in *.
assert (E2a : ew E 2 = getr regs3 2) by (unfold E; exact (ew_Ereg_nat regs3 _ 2 2%bv eq_refl)).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite E2a, R2; apply unsigned_lit_small; lia).
assert (E34 : ew E 34 = w64 (cx_v cx + Z.of_nat d)) by (unfold E; exact (ew_Ereg_extra regs3 _ 2)).
assert (E35 : ew E 35 = w64 (Z.of_nat d)) by (unfold E; exact (ew_Ereg_extra regs3 _ 3)).
assert (E19 : ew E 19 = w64 (cx_t cx + Z.of_nat (S p3) + Z.of_nat o))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 19 19%bv eq_refl); exact R19).
assert (SHOK : sh_ok tfibsegs PL_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 PL_N) mem3 (seg_rom tfibsegs))))) by constructor.
(* the declaration does not match: the local name is not plain *)
assert (Hne : skipn o (cx_ub cx) <> [])
  by (intros Hnil; apply (f_equal (@length Z)) in Hnil; rewrite length_skipn in Hnil; cbn in Hnil; lia).
assert (Hfa : forallb plain_ok (skipn o (cx_ub cx)) = false).
{ apply (pl_forallb_false plain_ok _ q); [rewrite length_skipn; lia|].
  rewrite pl_nth_skipn. exact Hnp. }
assert (Hmatch : matches (cx_tb cx) (cx_ub cx) (S p3) o = false).
{ rewrite (pl_matches _ _ _ _ Ho HFirst), (pl_plain_name _ Hne HLast). exact Hfa. }
unfold rd_decl in HDECL. cbv zeta in HDECL.
destruct HDECL as (Hhead & Hs11 & Hsp & Hp1 & Hp2 & Hc58 & Hp3 & Hc60 & Hlen3).
assert (Hdecl : decl (cx_tb cx) i = DFound p1 (p2 - p1) (S p3) o (S p3 + o))
  by exact (pl_decl_found (cx_tb cx) i s11 p1 p2 p3 o Hhead Hsp Hp1 Hp2 Hc58 Hp3 Hc60 HFI).
destruct (pl_sc_nomatch (cx_tb cx) (cx_ub cx) i d f p1 (p2 - p1) (S p3) o (S p3 + o) Hilt Hdecl Hmatch)
  as [Hscan Hread].
change (unpoison [] mem3) with mem3 in HJ.
unfold cfg_at. change (w64 PL_N) with (Z_to_bv 64 PL_N).
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 PL_N) mem3 (seg_rom tfibsegs))) in HJ.
aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan RD_L; [pl_awr U2|].
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ pl_win cx (cx_F cx) a ->
  aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (g3_aview_frame E (ss_mem (ss_BP PL_N)) (w_H W3) mem3 (ms_mem ms) HFr a Ha).
  intros (rr & Hin & Hr). cbn [ss_BP ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [pl_fr_ro pl_fr_rp pl_fr_d YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite U2 in Hr; apply Hn; unfold pl_win; lia. }
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_KEPT HS
  ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
assert (HPR : pl_regs_same regs3 (ms_regs ms)) by exact (pl_regs_same_of_kept regs3 (ms_regs ms) KR).
(* the two frame cells, read back out of the regions *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRrp;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
  cbn [ms_mem restrict] in HRrp, HRd end.
assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
{ replace (cx_sp cx) with (cx_F cx + 208) by lia.
  apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 208 8%N (SOff 34 0) (cx_v cx + Z.of_nat d) HRrp
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E34, Z.add_0_r; unfold w64;
          rewrite Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (Vd : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (cx_F cx + 8) 8 (Z.of_nat d)).
{ apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 8 8%N (SOff 35 0) (Z.of_nat d) HRd
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, Z.add_0_r; unfold w64;
          rewrite Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply (HSEGL cx (S (S p3 + o)) d ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ HB).
split; [|split; [|split]].
- apply pl_loop_of_mid.
  exact (pl_mid_kept cx d d (cx_v cx + Z.of_nat d) (cx_v cx + Z.of_nat d) ly3 S3 W3 regs3 mem3 _
    (ms_regs ms) (ms_mem ms) _ (cx_F cx) HMID HJ ltac:(lia) ltac:(lia) HFlo HFhi KE HPR Vrp Vd Hdle).
- destruct HACC as (Hi1 & Hi2 & Hi3 & Hi4).
  split; [lia|]. split; [lia|]. split; [rewrite Hi3; exact Hscan|]. rewrite Hi4, Hread. lia.
- rreg HS (20%bv : bv 5) Q20. rewrite Q20. reflexivity.
- rreg HS (24%bv : bv 5) Q24. rewrite Q24. cbn [sv_denot ew ewset Nat.eqb].
  rewrite E19, unsigned_lit_small by lia. unfold w64. f_equal. lia.
Qed.


Definition PL_KEPT3 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 27]%bv.

Lemma pl_from_P : forall f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3,
  rd_seg_L B CTX f -> rd_seg_PL B CTX (S f) m -> (length (cx_ub cx) - o - q <= S m)%nat ->
  rd_base B CTX cx ->
  rd_PL B cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 ->
  getr regs3 27 = w64 (byte_at (cx_ub cx) (o + q)) ->
  plain_ok (byte_at (cx_ub cx) (o + q)) = true ->
  SRr tfibsegs W3 (cfg_at tfibsegs PL_P regs3 mem3 md3) (rd_post B cx).
Proof.
intros f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 HSEGL HSEGPL Hm HB HPL R27 Hpl.
pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs. pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (CC & _).
unfold rd_PL in HPL. cbv zeta in HPL.
destruct HPL as (HLOOP & HACC & Hilt & HDECL & HFI & Ho & HFirst & HLast & Hqn & HPlainq & HS38 & R19 & R20 &
  R21 & R22 & R23 & R24 & R25 & R26).
pose proof HLOOP as HMID.
pose proof HMID as (HCOM & R9 & R18 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof HCOM as (HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HB as (HAN & HCTX & HROb & H10b & H11b & H12b & Hpresb & Htopr & Hvb & Hv63 & Ctb & Cub & Ktb & Kub &
  Hub255 & Htbmax & HGb & Hlv & Hcntb & Hevb & Hlbb).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARj & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (HSP : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (HFlo : alloc_ceiling + 4096 <= cx_F cx) by lia.
assert (HFhi : cx_sp cx + 16 <= 2 ^ 47) by lia.
assert (HF16 : cx_F cx mod 16 = 0) by
  (rewrite HFsp; replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia; rewrite Z_mod_plus_full;
   rewrite HSP; exact Hal16).
pose proof Ct as ((_ & _) & Ht1 & Ht2 & _).
pose proof Cu as ((HGu & HNZu) & Hu1 & Hu2 & _).
assert (Hclose : (S p3 + o < length (cx_tb cx))%nat) by
  (pose proof (pl_find_idx_lt _ _ _ HFI) as Hlt; rewrite length_skipn in Hlt; lia).
assert (Hoq : (o + q < length (cx_ub cx))%nat) by lia.
unfold rd_slots_ok in HSLOTS. rewrite pl_loc_list in HSLOTS.
apply Forall_cons_iff in HSLOTS as [SL0 HSLOTS]. apply Forall_cons_iff in HSLOTS as [SL8 HSLOTS].
cbv [pl_rest] in HSLOTS.
apply Forall_cons_iff in HSLOTS as [SL18 HSLOTS]. apply Forall_cons_iff in HSLOTS as [SL20 HSLOTS].
apply Forall_cons_iff in HSLOTS as [SL30 HSLOTS]. apply Forall_cons_iff in HSLOTS as [SL40 HSLOTS].
cbn [fst snd] in SL0, SL8, SL18, SL20, SL30, SL40.
pose proof HS38 as HS38'.
unfold rd_slots_ok in HS38'. apply Forall_cons_iff in HS38' as [SL38 _]. cbn [fst snd] in SL38.
destruct (HGu (o + q)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
rewrite app_nth1 in Vc, Rc by lia.
pose proof (plB_entry W3 PL_P regs3 mem3 (cx_F cx) (cx_u cx + Z.of_nat o + Z.of_nat q)
  (byte_at (cx_ub cx) (o + q)) (bv_unsigned (getr regs3 10)) (Z.of_nat d)
  (Z.of_nat (length (cx_ub cx) - o) - Z.of_nat q)
  (cx_u cx + Z.of_nat o) (cx_t cx) (cx_v cx + Z.of_nat d) (Z.of_nat d)
  R2 R8 ltac:(rewrite R20; unfold w64; f_equal; lia) R21 R25 R24 R26 R27
  ltac:(unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity)
  ltac:(lia) HF16 ltac:(lia) ltac:(unfold byte_at; lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  (proj1 SL18) (proj1 SL38) (proj1 SL40)
  ltac:(replace (cx_F cx + 208) with (cx_sp cx) by lia; exact HRP) (proj1 SL8)
  ltac:(intros a Ha; apply (apresent_writable tfibsegs); apply Hpresj; lia)
  ltac:(intros a Ha; apply (apresent_writable tfibsegs); apply Hpresj; lia)) as HS.
set (E := Ereg regs3 [w64 (cx_u cx + Z.of_nat o); w64 (cx_t cx); w64 (cx_v cx + Z.of_nat d);
  w64 (Z.of_nat d)]) in *.
assert (E2a : ew E 2 = getr regs3 2) by (unfold E; exact (ew_Ereg_nat regs3 _ 2 2%bv eq_refl)).
assert (E2b : ew E 2 = w64 (cx_F cx)) by (rewrite E2a; exact R2).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite E2b; apply unsigned_lit_small; lia).
assert (E3a : ew E 3 = getr regs3 3) by (unfold E; exact (ew_Ereg_nat regs3 _ 3 3%bv eq_refl)).
assert (E4a : ew E 4 = getr regs3 4) by (unfold E; exact (ew_Ereg_nat regs3 _ 4 4%bv eq_refl)).
assert (E8a : ew E 8 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl); exact R8).
assert (E19 : ew E 19 = w64 (cx_t cx + Z.of_nat (S p3) + Z.of_nat o))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 19 19%bv eq_refl); exact R19).
assert (E21 : ew E 21 = w64 (cx_u cx + Z.of_nat o + Z.of_nat q))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 21 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 (cx_t cx + Z.of_nat p1))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 22 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = w64 (Z.of_nat p2 - Z.of_nat p1))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 23 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = w64 (Z.of_nat d))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 24 24%bv eq_refl); exact R24).
assert (E26 : ew E 26 = w64 (Z.of_nat (length (cx_ub cx) - o) - Z.of_nat q))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 26 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = w64 (byte_at (cx_ub cx) (o + q)))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = w64 (cx_u cx + Z.of_nat o)) by (unfold E; exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = w64 (cx_t cx)) by (unfold E; exact (ew_Ereg_extra regs3 _ 1)).
assert (E34 : ew E 34 = w64 (cx_v cx + Z.of_nat d)) by (unfold E; exact (ew_Ereg_extra regs3 _ 2)).
assert (E35 : ew E 35 = w64 (Z.of_nat d)) by (unfold E; exact (ew_Ereg_extra regs3 _ 3)).
assert (Hne : skipn o (cx_ub cx) <> [])
  by (intros Hnil; apply (f_equal (@length Z)) in Hnil; rewrite length_skipn in Hnil; cbn in Hnil; lia).
pose proof HDECL as HDECL2. unfold rd_decl in HDECL2. cbv zeta in HDECL2.
destruct HDECL2 as (Hhead & Hs11 & Hsp & Hp1 & Hp2 & Hc58 & Hp3 & Hc60 & Hlen3).
assert (Hdecl : decl (cx_tb cx) i = DFound p1 (p2 - p1) (S p3) o (S p3 + o))
  by exact (pl_decl_found (cx_tb cx) i s11 p1 p2 p3 o Hhead Hsp Hp1 Hp2 Hc58 Hp3 Hc60 HFI).
assert (Hub0 : (length (cx_ub cx) =? 0)%nat = false) by (destruct (cx_ub cx); [congruence | reflexivity]).
assert (Hcf0 : (cx_cnt cx =? cx_fail cx) = false) by (apply Z.eqb_neq; exact Hcf).
assert (SHOK : sh_ok tfibsegs PL_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 PL_P) mem3 (seg_rom tfibsegs))))) by constructor.
change (unpoison [] mem3) with mem3 in HJ.
unfold cfg_at. change (w64 PL_P) with (Z_to_bv 64 PL_P).
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 PL_P) mem3 (seg_rom tfibsegs))) in HJ.
aj_run_tok rd_tbl_ok HS HJ SHOK PL_Bspan; [pl_awr U2|].
assert (KE1 : pl_same cx W3 mem3 (ms_mem ms)).
{ intros a Ha Hn. apply (g3_aview_frame E (ss_mem (ss_BP PL_P)) (w_H W3) mem3 (ms_mem ms) HFr a Ha).
  intros (rr & Hin & Hr). cbn [ss_BP ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [pl_fr_ro pl_fr_rp pl_fr_d YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite U2 in Hr; apply Hn; unfold pl_win; lia. }
srr_branch_tok rd_tbl_ok HS SHOK PL_Bspan.
{ (* bytes left: the back edge at 0x81fc8 *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom_off _ 26 (Z.of_nat (length (cx_ub cx) - o) - Z.of_nat q) (-1)
    ltac:(cbn [ew ewset Nat.eqb]; exact E26) ltac:(lia) ltac:(lia)) in Hc.
  rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  assert (HqS : (S q < length (cx_ub cx) - o)%nat) by lia.
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan PL_A; [pl_awr U2|].
lazymatch type of HFr0 with frame_of ?Ex ?rs _ _ =>
  assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
  assert (KE2 : pl_same cx W3 (ms_mem ms) (ms_mem ms0)) by
    (intros a Ha Hn; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms) (ms_mem ms0) HFr0 a Ha);
     intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
     destruct Hin as [<-|[<-|[<-|[]]]];
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr;
       apply Hn; unfold pl_win; lia);
  clear X2 end.
assert (KE : pl_same cx W3 mem3 (ms_mem ms0)) by exact (pl_same_trans cx W3 _ _ _ KE1 KE2).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRrp;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
  cbn [ms_mem restrict] in HRrp, HRd end.
assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms0)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
{ replace (cx_sp cx) with (cx_F cx + 208) by lia.
  apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 208 8%N (SOff 34 0) (cx_v cx + Z.of_nat d) HRrp
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E34, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (Vd : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms0)) (cx_F cx + 8) 8 (Z.of_nat d)).
{ apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 8 8%N (SOff 35 0) (Z.of_nat d) HRd
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_KEPT3 HS
  ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
assert (HPR : pl_regs_same regs3 (ms_regs ms0)).
{ apply pl_regs_same_of_kept. intros r Hr. apply KR. cbv [PL_KEPT PL_KEPT2 PL_KEPT3 In] in Hr |- *. tauto. }
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  eapply (HSEGPL cx i d s11 p1 p2 p3 o (S q) ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) _ ltac:(lia) HB).
  unfold rd_PL. cbv zeta.
  split.
  { apply pl_loop_of_mid.
    exact (pl_mid_kept cx d d (cx_v cx + Z.of_nat d) (cx_v cx + Z.of_nat d) ly3 S3 W3 regs3 mem3 _
      (ms_regs ms0) (ms_mem ms0) _ (cx_F cx) HMID HJ ltac:(lia) ltac:(lia) HFlo HFhi KE HPR Vrp Vd Hdle). }
  split; [exact HACC|]. split; [exact Hilt|]. split; [exact HDECL|]. split; [exact HFI|]. split; [exact Ho|].
  split; [exact HFirst|]. split; [exact HLast|]. split; [exact HqS|].
  split.
  { apply (pl_forallb_S plain_ok _ q); [rewrite length_skipn; lia | exact HPlainq|].
    rewrite pl_nth_skipn. exact Hpl. }
  split.
  { apply (pl_slots_kept cx W3 W3 mem3 (ms_mem ms0) _ HS38). intros ss Hss j Hj. cbn in Hj.
    cbv [In] in Hss. destruct Hss as [<-|[]]. cbn [fst]. apply KE; [lia | unfold pl_win; lia]. }
  split; [rewrite (KR 19%bv ltac:(pl_in)); exact R19|].
  split; [rreg HS (20%bv : bv 5) Q20; rewrite Q20; cbn [sv_denot ew ewset Nat.eqb];
          rewrite E2b, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
  split; [rreg HS (21%bv : bv 5) Q21; rewrite Q21; cbn [sv_denot ew ewset Nat.eqb];
          rewrite E21, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
  split; [rewrite (KR 22%bv ltac:(pl_in)); exact R22|].
  split; [rewrite (KR 23%bv ltac:(pl_in)); exact R23|].
  split; [rewrite (KR 24%bv ltac:(pl_in)); exact R24|].
  split; [rreg HS (25%bv : bv 5) Q25; rewrite Q25; cbn [sv_denot ew ewset Nat.eqb];
          rewrite E21, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
  rreg HS (26%bv : bv 5) Q26. rewrite Q26. cbn [sv_denot ew ewset Nat.eqb].
  rewrite E26, unsigned_lit_small by lia. unfold w64. f_equal. lia. }
{ (* the last byte: the declaration matches the uri *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom_off _ 26 (Z.of_nat (length (cx_ub cx) - o) - Z.of_nat q) (-1)
    ltac:(cbn [ew ewset Nat.eqb]; exact E26) ltac:(lia) ltac:(lia)) in Hc.
  rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  assert (HFall : firstn (S q) (skipn o (cx_ub cx)) = skipn o (cx_ub cx))
    by (apply firstn_all2; rewrite length_skipn; lia).
  assert (Hall : forallb plain_ok (skipn o (cx_ub cx)) = true).
  { rewrite <- HFall. apply (pl_forallb_S plain_ok _ q); [rewrite length_skipn; lia | exact HPlainq|].
    rewrite pl_nth_skipn. exact Hpl. }
  assert (Hmatch : matches (cx_tb cx) (cx_ub cx) (S p3) o = true).
  { rewrite (pl_matches _ _ _ _ Ho HFirst), (pl_plain_name _ Hne HLast). exact Hall. }
  aj_run_tok rd_tbl_ok HS HJ SHOK PL_Bspan; [pl_awr U2|].
lazymatch type of HFr0 with frame_of ?Ex ?rs _ _ =>
  assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
  assert (KE2 : pl_same cx W3 (ms_mem ms) (ms_mem ms0)) by
    (intros a Ha Hn; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms) (ms_mem ms0) HFr0 a Ha);
     intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
     destruct Hin as [<-|[<-|[<-|[]]]];
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr;
       apply Hn; unfold pl_win; lia);
  clear X2 end.
assert (KE : pl_same cx W3 mem3 (ms_mem ms0)) by exact (pl_same_trans cx W3 _ _ _ KE1 KE2).
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (H24' : ew Ex 24 = Z_to_bv 64 (Z.of_nat d)) by (cbn [ew ewset Nat.eqb]; exact E24) end.
  srr_branch_tok rd_tbl_ok HS SHOK PL_Bspan.
  { (* read_again is already at its bound: the answer is 1 *)
    erewrite (pl_D_of 24 _ (Z.of_nat d) _ _ _ H24') in Hc0 by reflexivity.
    rewrite (pl_D_d (Z.of_nat d) ltac:(lia)) in Hc0. apply Z.ltb_lt in Hc0.
    destruct (pl_sc_cnt (cx_tb cx) (cx_ub cx) i d f p1 (p2 - p1) (S p3) o (S p3 + o) Hilt Hdecl Hmatch
      ltac:(lia)) as [Hscan Hread].
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan RD_R; [pl_awr U2|].
lazymatch type of HFr1 with frame_of ?Ex ?rs _ _ =>
  assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
  assert (KE3 : pl_same cx W3 (ms_mem ms0) (ms_mem ms1)) by
    (intros a Ha Hn; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha);
     intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
     destruct Hin as [<-|[<-|[<-|[]]]];
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr;
       apply Hn; unfold pl_win; lia);
  clear X2 end.
assert (KEb : pl_same cx W3 mem3 (ms_mem ms1)) by exact (pl_same_trans cx W3 _ _ _ KE KE3).
    clear KE. rename KEb into KE.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRrp;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
  cbn [ms_mem restrict] in HRrp, HRd end.
assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms1)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
{ replace (cx_sp cx) with (cx_F cx + 208) by lia.
  apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 208 8%N (SOff 34 0) (cx_v cx + Z.of_nat d) HRrp
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E34, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (Vd : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms1)) (cx_F cx + 8) 8 (Z.of_nat d)).
{ apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 8 8%N (SOff 35 0) (Z.of_nat d) HRd
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_KEPT HS
  ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
assert (HPR : pl_regs_same regs3 (ms_regs ms1)).
{ apply pl_regs_same_of_kept. intros r Hr. apply KR. cbv [PL_KEPT PL_KEPT2 PL_KEPT3 In] in Hr |- *. tauto. }
    assert (KL : g3_low_kept W3 W3 mem3 (ms_mem ms1))
      by (intros a Ha; apply KE; [lia | unfold pl_win; lia]).
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
    eapply (rd_ret_holds B CTX cx EV_names ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ 1 HB).
    - exact (pl_com_kept cx EV_names ly3 S3 W3 regs3 mem3 _ (ms_regs ms1) (ms_mem ms1) _ (cx_F cx)
        HCOM HJ ltac:(lia) ltac:(lia) HFlo HFhi KE HPR).
    - rreg HS (21%bv : bv 5) Q21. rewrite Q21. reflexivity.
    - lia.
    - split; [exact HPERM|]. split.
      + right. right. split; [exact Hub|]. split; [exact Hcf|]. split.
        * destruct HACC as (_ & _ & Hnames & _). symmetry. rewrite Hnames. exact Hscan.
        * exact (g3_fm_glob_kept W3 W3 mem3 (ms_mem ms1) _ _ _ _ HGL KL).
      + rewrite Hub0, Hcf0. cbn [orb]. destruct HACC as (_ & _ & _ & Hnr). rewrite Hnr, Hread.
        rewrite Nat.add_0_r. exact Vrp. }
  { (* one more reading: ++*readings, then has_prefixed *)
    erewrite (pl_D_of 24 _ (Z.of_nat d) _ _ _ H24') in Hc0 by reflexivity.
    rewrite (pl_D_d (Z.of_nat d) ltac:(lia)) in Hc0. apply Z.ltb_ge in Hc0.
    assert (Hd16 : (d < 16)%nat) by lia.
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan A_has_prefixed;
      [ | pl_awr U2 | ].
    { (* the 8-byte check of *readings *)
      lazymatch goal with |- range_addressable _ (U ?Ex _) _ _ =>
        assert (Y2 : U Ex (SOff 2 208) = cx_F cx + 208) by
          (apply (U_atom_off Ex 2 (cx_F cx) 208); [cbn [ew ewset Nat.eqb]; exact E2b | lia | lia]);
        apply (obl_of_range tfibsegs (w_H W3) (ms_mem ms0) Ex PL_Bx (U Ex (SOff 2 208)) 8 (cx_sp cx) 8);
        [ | unfold PL_Bx; apply (U_atom Ex 8 SHADOW_OFF);
            [cbn [ew ewset Nat.eqb]; exact E8a | unfold SHADOW_OFF; lia]
          | rewrite Y2; lia | rewrite Y2; lia ] end.
      apply (zero_shadow_range (aview tfibsegs (w_H W3) (ms_mem ms0)) SHADOW_OFF (cx_sp cx) 8);
        [rewrite HSP; replace (spZ (cx_regs cx)) with (spZ (cx_regs cx) + 0) by lia; rewrite <- HSP;
         replace (cx_sp cx + 0) with (cx_sp cx) by lia;
         replace (cx_sp cx) with (cx_sp cx + 16 - 16) by lia; rewrite <- Z.add_opp_r;
         apply Z.mod_divide in Hal16; [|lia]; destruct Hal16 as [kk Hkk]; rewrite HSP in *; lia
        | reflexivity | ].
      intros j Hj. assert (j = 0) by (cbn in Hj; lia). subst j. rewrite Z.add_0_r.
      change (shadow_of_addr SHADOW_OFF (cx_sp cx)) with (shadow_addr (cx_sp cx)).
      apply (g3_stk_sh0_of_AR B ly3 S3 W3 (ms_mem ms0) _ (cx_sp cx) (cx_sp cx + 1) (proj1 HJ)
        ltac:(rewrite Eslo; lia) ltac:(rewrite Eshi; lia)). lia. }
lazymatch type of HFr1 with frame_of ?Ex ?rs _ _ =>
  assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
  assert (KE3 : pl_same cx W3 (ms_mem ms0) (ms_mem ms1)) by
    (intros a Ha Hn; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha);
     intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
     destruct Hin as [<-|[<-|[<-|[]]]];
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr;
       apply Hn; unfold pl_win; lia);
  clear X2 end.
assert (KEb : pl_same cx W3 mem3 (ms_mem ms1)) by exact (pl_same_trans cx W3 _ _ _ KE KE3).
    clear KE. rename KEb into KE.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRrp;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
  cbn [ms_mem restrict] in HRrp, HRd end.
assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms1)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d + 1)).
{ replace (cx_sp cx) with (cx_F cx + 208) by lia.
  apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 208 8%N (SOff 34 1) (cx_v cx + Z.of_nat d + 1) HRrp
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E34, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (Vd : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms1)) (cx_F cx + 8) 8 (Z.of_nat d)).
{ apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 8 8%N (SOff 35 0) (Z.of_nat d) HRd
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_KEPT HS
  ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
assert (HPR : pl_regs_same regs3 (ms_regs ms1)).
{ apply pl_regs_same_of_kept. intros r Hr. apply KR. cbv [PL_KEPT PL_KEPT2 PL_KEPT3 In] in Hr |- *. tauto. }
    eassert (HCOMc : rd_com B cx EV_names [] ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _)
      by exact (pl_com_kept cx EV_names ly3 S3 W3 regs3 mem3 _ (ms_regs ms1) (ms_mem ms1) _ (cx_F cx)
        HCOM HJ ltac:(lia) ltac:(lia) HFlo HFhi KE HPR).
    pose proof HCOMc as (HJc & _ & Rc2 & Rc3 & Rc4 & Rc8 & _ & _ & HROc & Ctc & Cuc & Ktc & Kuc).
    assert (HGLc : fm_glob tfibsegs W3 (ms_mem ms1) (cx_live cx)
      (Z.max (cx_peak cx) (cx_live cx + cx_ulen cx + 3)) (cx_cnt cx + 1) (cx_fail cx)).
    { apply (g3_fm_glob_kept W3 W3 mem3 (ms_mem ms1) _ _ _ _ HGL).
      intros a Ha. apply KE; [lia | unfold pl_win; lia]. }
    rreg HS (1%bv : bv 5) Qra. rreg HS (2%bv : bv 5) Qsp. rreg HS (8%bv : bv 5) Qs0.
    rreg HS (10%bv : bv 5) Qa0. rreg HS (11%bv : bv 5) Qa1. rreg HS (12%bv : bv 5) Qa2.
    rreg HS (13%bv : bv 5) Qa3. rreg HS (19%bv : bv 5) Q19. rreg HS (21%bv : bv 5) Q21.
    rreg HS (24%bv : bv 5) Q24.
    assert (Hsp1 : spZ (ms_regs ms1) = cx_F cx)
      by (unfold spZ; rewrite Qsp; cbn [ew ewset Nat.eqb]; exact U2).
    eassert (HPRE1 : afn_pre tfibsegs B STK_has_prefixed ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ []).
    { eapply (afn_pre_at tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx)
        (cx_W cx) (cx_mem cx) (cx_md cx) [] ly3 S3 W3 (ms_mem ms1) _ EV_names (ms_regs ms1)
        STK_has_prefixed (-224) [] HJ).
      - rewrite Hsp1. lia.
      - reflexivity.
      - lia.
      - unfold STK_has_prefixed, STK_RT_STRSTR, STK_RT_STR, STK_name_char, STK_RT_ISALNUM, ESTACK. lia.
      - unfold STK_has_prefixed, STK_RT_STRSTR, STK_RT_STR, STK_name_char, STK_RT_ISALNUM, ESTACK. lia.
      - rewrite Qra. vm_compute. reflexivity.
      - unfold raZ. rewrite Qra. rewrite unsigned_lit_small by lia. lia.
      - rewrite Rc3. exact Hgp.
      - rewrite Rc4. exact Htp.
      - apply achain_low. unfold s0Z. rewrite Qs0. cbn [ew ewset Nat.eqb]. rewrite E8a.
        rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold SHADOW_OFF. lia. }
    assert (Hlb : skipn o (cx_ub cx) <> []) by exact Hne.
    assert (Hcsu : cstr_ok tfibsegs W3 (ms_mem ms1) (cx_u cx + Z.of_nat o) (skipn o (cx_ub cx)))
      by exact (pl_cstr_ok_suffix W3 (ms_mem ms1) (cx_u cx) (cx_ub cx) o ltac:(lia) Cuc).
    assert (Hcku : cstr_kept B ly3 S3 (cx_u cx + Z.of_nat o) (skipn o (cx_ub cx)))
      by exact (g3_cstr_kept_suffix B ly3 S3 (cx_u cx) (cx_ub cx) o Kuc ltac:(lia)).
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
    eapply SRr_bind.
    { apply (HASP ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ [] (cx_t cx) (Z.of_nat p1)
        (Z.of_nat p2 - Z.of_nat p1) (cx_u cx + Z.of_nat o) (cx_tb cx) (skipn o (cx_ub cx))
        (cx_live cx) (Z.max (cx_peak cx) (cx_live cx + cx_ulen cx + 3)) (cx_cnt cx + 1) (cx_fail cx)).
      - split; [exact HPRE1 | exact HROc].
      - exact HGLc.
      - rewrite Qa0. cbn [ew ewset Nat.eqb]. exact E33.
      - rewrite Qa1. cbn [ew ewset Nat.eqb]. exact E22.
      - rewrite Qa2. cbn [ew ewset Nat.eqb]. exact E23.
      - rewrite Qa3. cbn [ew ewset Nat.eqb]. exact E32.
      - exact Ctc.
      - exact Hcsu.
      - exact Ktc.
      - exact Hcku.
      - exact Hlb.
      - lia.
      - lia.
      - lia.
      - exact Htbmax. }
    cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & Hc5 & HJ5 & HP5 & H10' & Hablk & HGL5).
    subst c5. rewrite Qra.
    assert (Hq1 : Z.to_nat (Z.of_nat p1) = p1) by (rewrite Nat2Z.id; reflexivity).
    assert (Hq2 : Z.to_nat (Z.of_nat p2 - Z.of_nat p1) = (p2 - p1)%nat)
      by (rewrite <- Nat2Z.inj_sub by lia; rewrite Nat2Z.id; reflexivity).
    rewrite Hq1, Hq2 in H10'.
    pose proof (pl_regs_pl_of_pres (ms_regs ms1) regs5 HP5) as HP5a.
    pose proof HP5a as (HP5s & P19 & _ & P21 & _ & _ & P24 & _).
    pose proof (g3_ajsub_img_ok B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx)
      (cx_W cx) (cx_mem cx) (cx_md cx) [] ly3 S3 W3 (ms_mem ms1) _ EV_names STK_has_prefixed
      (spZ (ms_regs ms1)) [] [] ly5 S5 W5 mem5 md5 0 HJ HJ5 ltac:(rewrite Hsp1; unfold STK_has_prefixed,
        STK_RT_STRSTR, STK_RT_STR, STK_name_char, STK_RT_ISALNUM, ESTACK; lia)
      ltac:(rewrite Hsp1; lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ6.
    cbn [app] in HJ6. rewrite Z.add_0_r in HJ6.
    rewrite Hsp1 in HJ5.
    eapply (pl_from_C f cx i d s11 p1 p2 p3 o ly5 S5 W5 regs5 mem5 md5 _ HSEGL HB).
    - split.
      { eapply (pl_mid_hp cx d (cx_v cx + Z.of_nat d + 1) ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _
          ly5 S5 W5 regs5 mem5 md5 IMG); [|exact HJ5|exact HJ6|exact Hablk|exact HP5s|exact HGL5|lia|lia].
        exact (pl_mid_kept cx d d (cx_v cx + Z.of_nat d) (cx_v cx + Z.of_nat d + 1) ly3 S3 W3 regs3 mem3 _
          (ms_regs ms1) (ms_mem ms1) _ (cx_F cx) HMID HJ ltac:(lia) ltac:(lia) HFlo HFhi KE HPR Vrp Vd
          Hdle). }
      split; [exact HACC|]. split; [exact Hilt|]. split; [exact HDECL|]. split; [exact HFI|].
      split; [exact Ho|]. split; [exact HFirst|]. split; [exact HLast|]. split; [exact Hall|].
      split; [exact Hd16|].
      split; [rewrite P19, Q19; cbn [ew ewset Nat.eqb]; exact E19|].
      split; [rewrite P21, Q21; reflexivity|].
      rewrite P24, Q24. cbn [ew ewset Nat.eqb]. exact E24.
    - exact H10'.
    - reflexivity. } }
Qed.


Lemma pl_from_B : forall f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 vv,
  rd_seg_L B CTX f -> rd_seg_PL B CTX (S f) m -> (length (cx_ub cx) - o - q <= S m)%nat ->
  rd_base B CTX cx ->
  rd_PL B cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 ->
  getr regs3 27 = w64 (byte_at (cx_ub cx) (o + q)) ->
  getr regs3 10 = w64 vv -> 0 <= vv < 2 ^ 64 ->
  (vv <> 0 <-> is_alnum (byte_at (cx_ub cx) (o + q)) = true) ->
  SRr tfibsegs W3 (cfg_at tfibsegs PL_B regs3 mem3 md3) (rd_post B cx).
Proof.
intros f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 vv HSEGL HSEGPL Hm HB HPL R27 R10 Hvv Hal.
pose proof HPL as HPL0.
pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs. pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (CC & _).
unfold rd_PL in HPL. cbv zeta in HPL.
destruct HPL as (HLOOP & HACC & Hilt & HDECL & HFI & Ho & HFirst & HLast & Hqn & HPlainq & HS38 & R19 & R20 &
  R21 & R22 & R23 & R24 & R25 & R26).
pose proof HLOOP as HMID.
pose proof HMID as (HCOM & R9 & R18 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof HCOM as (HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HB as (HAN & HCTX & HROb & H10b & H11b & H12b & Hpresb & Htopr & Hvb & Hv63 & Ctb & Cub & Ktb & Kub &
  Hub255 & Htbmax & HGb & Hlv & Hcntb & Hevb & Hlbb).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARj & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (HSP : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (HFlo : alloc_ceiling + 4096 <= cx_F cx) by lia.
assert (HFhi : cx_sp cx + 16 <= 2 ^ 47) by lia.
assert (HF16 : cx_F cx mod 16 = 0) by
  (rewrite HFsp; replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia; rewrite Z_mod_plus_full;
   rewrite HSP; exact Hal16).
pose proof Ct as ((_ & _) & Ht1 & Ht2 & _).
pose proof Cu as ((HGu & HNZu) & Hu1 & Hu2 & _).
assert (Hclose : (S p3 + o < length (cx_tb cx))%nat) by
  (pose proof (pl_find_idx_lt _ _ _ HFI) as Hlt; rewrite length_skipn in Hlt; lia).
assert (Hoq : (o + q < length (cx_ub cx))%nat) by lia.
unfold rd_slots_ok in HSLOTS. rewrite pl_loc_list in HSLOTS.
apply Forall_cons_iff in HSLOTS as [SL0 HSLOTS]. apply Forall_cons_iff in HSLOTS as [SL8 HSLOTS].
cbv [pl_rest] in HSLOTS.
apply Forall_cons_iff in HSLOTS as [SL18 HSLOTS]. apply Forall_cons_iff in HSLOTS as [SL20 HSLOTS].
apply Forall_cons_iff in HSLOTS as [SL30 HSLOTS]. apply Forall_cons_iff in HSLOTS as [SL40 HSLOTS].
cbn [fst snd] in SL0, SL8, SL18, SL20, SL30, SL40.
pose proof HS38 as HS38'.
unfold rd_slots_ok in HS38'. apply Forall_cons_iff in HS38' as [SL38 _]. cbn [fst snd] in SL38.
destruct (HGu (o + q)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
rewrite app_nth1 in Vc, Rc by lia.
pose proof (plB_entry W3 PL_B regs3 mem3 (cx_F cx) (cx_u cx + Z.of_nat o + Z.of_nat q)
  (byte_at (cx_ub cx) (o + q)) (bv_unsigned (getr regs3 10)) (Z.of_nat d)
  (Z.of_nat (length (cx_ub cx) - o) - Z.of_nat q)
  (cx_u cx + Z.of_nat o) (cx_t cx) (cx_v cx + Z.of_nat d) (Z.of_nat d)
  R2 R8 ltac:(rewrite R20; unfold w64; f_equal; lia) R21 R25 R24 R26 R27
  ltac:(unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity)
  ltac:(lia) HF16 ltac:(lia) ltac:(unfold byte_at; lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  (proj1 SL18) (proj1 SL38) (proj1 SL40)
  ltac:(replace (cx_F cx + 208) with (cx_sp cx) by lia; exact HRP) (proj1 SL8)
  ltac:(intros a Ha; apply (apresent_writable tfibsegs); apply Hpresj; lia)
  ltac:(intros a Ha; apply (apresent_writable tfibsegs); apply Hpresj; lia)) as HS.
set (E := Ereg regs3 [w64 (cx_u cx + Z.of_nat o); w64 (cx_t cx); w64 (cx_v cx + Z.of_nat d);
  w64 (Z.of_nat d)]) in *.
assert (E2a : ew E 2 = getr regs3 2) by (unfold E; exact (ew_Ereg_nat regs3 _ 2 2%bv eq_refl)).
assert (E2b : ew E 2 = w64 (cx_F cx)) by (rewrite E2a; exact R2).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite E2b; apply unsigned_lit_small; lia).
assert (E3a : ew E 3 = getr regs3 3) by (unfold E; exact (ew_Ereg_nat regs3 _ 3 3%bv eq_refl)).
assert (E4a : ew E 4 = getr regs3 4) by (unfold E; exact (ew_Ereg_nat regs3 _ 4 4%bv eq_refl)).
assert (E8a : ew E 8 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl); exact R8).
assert (E19 : ew E 19 = w64 (cx_t cx + Z.of_nat (S p3) + Z.of_nat o))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 19 19%bv eq_refl); exact R19).
assert (E21 : ew E 21 = w64 (cx_u cx + Z.of_nat o + Z.of_nat q))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 21 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 (cx_t cx + Z.of_nat p1))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 22 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = w64 (Z.of_nat p2 - Z.of_nat p1))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 23 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = w64 (Z.of_nat d))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 24 24%bv eq_refl); exact R24).
assert (E26 : ew E 26 = w64 (Z.of_nat (length (cx_ub cx) - o) - Z.of_nat q))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 26 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = w64 (byte_at (cx_ub cx) (o + q)))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = w64 (cx_u cx + Z.of_nat o)) by (unfold E; exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = w64 (cx_t cx)) by (unfold E; exact (ew_Ereg_extra regs3 _ 1)).
assert (E34 : ew E 34 = w64 (cx_v cx + Z.of_nat d)) by (unfold E; exact (ew_Ereg_extra regs3 _ 2)).
assert (E35 : ew E 35 = w64 (Z.of_nat d)) by (unfold E; exact (ew_Ereg_extra regs3 _ 3)).
assert (E10 : ew E 10 = w64 vv) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl); exact R10).
assert (Hcr : 0 <= byte_at (cx_ub cx) (o + q) < 256) by (unfold byte_at; lia).
assert (SHOK : sh_ok tfibsegs PL_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 PL_B) mem3 (seg_rom tfibsegs))))) by constructor.
change (unpoison [] mem3) with mem3 in HJ.
unfold cfg_at. change (w64 PL_B) with (Z_to_bv 64 PL_B).
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 PL_B) mem3 (seg_rom tfibsegs))) in HJ.
srr_branch_tok rd_tbl_ok HS SHOK PL_Bspan.
{ (* isalnum (c): the byte is plain *)
  rewrite branch_ne_U, (U_atom E 10 vv E10 Hvv) in Hc. rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  assert (Hpl : plain_ok (byte_at (cx_ub cx) (o + q)) = true) by (apply pl_alnum_plain; apply Hal; exact Hc).
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan PL_P; [pl_awr U2|].
assert (KE1 : pl_same cx W3 mem3 (ms_mem ms)).
{ intros a Ha Hn. apply (g3_aview_frame E _ (w_H W3) mem3 (ms_mem ms) HFr a Ha).
  intros (rr & Hin & Hr). cbn [ss_BP ss_mem add_cond In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [pl_fr_ro pl_fr_rp pl_fr_d YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite U2 in Hr; apply Hn; unfold pl_win; lia. }
  assert (KE : pl_same cx W3 mem3 (ms_mem ms)) by exact KE1.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRrp;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
  cbn [ms_mem restrict] in HRrp, HRd end.
assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
{ replace (cx_sp cx) with (cx_F cx + 208) by lia.
  apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 208 8%N (SOff 34 0) (cx_v cx + Z.of_nat d) HRrp
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E34, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (Vd : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (cx_F cx + 8) 8 (Z.of_nat d)).
{ apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 8 8%N (SOff 35 0) (Z.of_nat d) HRd
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_KEPT2 HS
  ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
assert (HPRpl : pl_regs_pl regs3 (ms_regs ms)).
{ apply pl_regs_pl_of_kept; [exact KR | |].
  - rreg HS (20%bv : bv 5) Q20. rewrite Q20, R20. cbn [sv_denot ew ewset Nat.eqb].
    rewrite U2. unfold w64. f_equal. lia.
  - rreg HS (25%bv : bv 5) Q25. rewrite Q25, R25. cbn [ew ewset Nat.eqb]. exact E21. }
assert (R27x : getr (ms_regs ms) 27 = w64 (byte_at (cx_ub cx) (o + q)))
  by (rewrite (KR 27%bv ltac:(pl_in)); exact R27).
pose proof (pl_PL_kept cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) _
  (cx_F cx) HPL0 HJ ltac:(lia) ltac:(lia) HFlo HFhi KE HPRpl Vrp Vd) as HPLx.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
exact (pl_from_P f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ HSEGL HSEGPL Hm HB HPLx R27x Hpl).
}
{ (* not alnum: c - 45 >u 50, then the mask bit *)
  rewrite branch_ne_U, (U_atom E 10 vv E10 Hvv) in Hc. rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  assert (Hnal : is_alnum (byte_at (cx_ub cx) (o + q)) = false).
  { destruct (is_alnum (byte_at (cx_ub cx) (o + q))) eqn:Ea; [|reflexivity].
    exfalso. exact (proj2 Hal eq_refl Hc). }
  aj_run_tok rd_tbl_ok HS HJ SHOK PL_Bspan; [pl_awr U2|].
assert (KE1 : pl_same cx W3 mem3 (ms_mem ms)).
{ intros a Ha Hn. apply (g3_aview_frame E _ (w_H W3) mem3 (ms_mem ms) HFr a Ha).
  intros (rr & Hin & Hr). cbn [ss_BP ss_mem add_cond In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [pl_fr_ro pl_fr_rp pl_fr_d YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite U2 in Hr; apply Hn; unfold pl_win; lia. }
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (H27a : ew Ex 27 = Z_to_bv 64 (byte_at (cx_ub cx) (o + q))) by (cbn [ew ewset Nat.eqb]; exact E27) end.
  srr_branch_tok rd_tbl_ok HS SHOK PL_Bspan.
  { (* c - 45 >u 50: not plain *)
    erewrite (pl_D_of 27 _ (byte_at (cx_ub cx) (o + q)) _ _ _ H27a) in Hc0 by reflexivity.
    pose proof (pl_cls_far _ Hcr Hnal Hc0) as Hnp.
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan PL_N; [pl_awr U2|].
lazymatch type of HFr0 with frame_of ?Ex ?rs _ _ =>
  assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
  assert (KE2 : pl_same cx W3 (ms_mem ms) (ms_mem ms0)) by
    (intros a Ha Hn; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms) (ms_mem ms0) HFr0 a Ha);
     intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
     destruct Hin as [<-|[<-|[<-|[]]]];
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr;
       apply Hn; unfold pl_win; lia);
  clear X2 end.
    assert (KE : pl_same cx W3 mem3 (ms_mem ms0)) by exact (pl_same_trans cx W3 _ _ _ KE1 KE2).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRrp;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
  cbn [ms_mem restrict] in HRrp, HRd end.
assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms0)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
{ replace (cx_sp cx) with (cx_F cx + 208) by lia.
  apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 208 8%N (SOff 34 0) (cx_v cx + Z.of_nat d) HRrp
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E34, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (Vd : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms0)) (cx_F cx + 8) 8 (Z.of_nat d)).
{ apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 8 8%N (SOff 35 0) (Z.of_nat d) HRd
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_KEPT2 HS
  ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
assert (HPRpl : pl_regs_pl regs3 (ms_regs ms0)).
{ apply pl_regs_pl_of_kept; [exact KR | |].
  - rreg HS (20%bv : bv 5) Q20. rewrite Q20, R20. cbn [sv_denot ew ewset Nat.eqb].
    rewrite U2. unfold w64. f_equal. lia.
  - rreg HS (25%bv : bv 5) Q25. rewrite Q25, R25. cbn [ew ewset Nat.eqb]. exact E21. }
assert (R27x : getr (ms_regs ms0) 27 = w64 (byte_at (cx_ub cx) (o + q)))
  by (rewrite (KR 27%bv ltac:(pl_in)); exact R27).
pose proof (pl_PL_kept cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 (ms_regs ms0) (ms_mem ms0) _
  (cx_F cx) HPL0 HJ ltac:(lia) ltac:(lia) HFlo HFhi KE HPRpl Vrp Vd) as HPLx.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
exact (pl_from_N f cx i d s11 p1 p2 p3 o q ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) _ HSEGL HB HPLx R27x Hnp).
  }
  { (* in range: the mask bit decides *)
    erewrite (pl_D_of 27 _ (byte_at (cx_ub cx) (o + q)) _ _ _ H27a) in Hc0 by reflexivity.
    aj_run_tok rd_tbl_ok HS HJ SHOK PL_Bspan; [pl_awr U2|].
lazymatch type of HFr0 with frame_of ?Ex ?rs _ _ =>
  assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
  assert (KE2 : pl_same cx W3 (ms_mem ms) (ms_mem ms0)) by
    (intros a Ha Hn; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms) (ms_mem ms0) HFr0 a Ha);
     intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
     destruct Hin as [<-|[<-|[<-|[]]]];
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr;
       apply Hn; unfold pl_win; lia);
  clear X2 end.
    assert (KEa : pl_same cx W3 mem3 (ms_mem ms0)) by exact (pl_same_trans cx W3 _ _ _ KE1 KE2).
    lazymatch type of HS with st_ok _ ?Ex _ _ =>
      assert (H27b : ew Ex 27 = Z_to_bv 64 (byte_at (cx_ub cx) (o + q))) by (cbn [ew ewset Nat.eqb]; exact E27) end.
    srr_branch_tok rd_tbl_ok HS SHOK PL_Bspan.
    { (* bit clear: not plain *)
      erewrite (pl_D_of 27 _ (byte_at (cx_ub cx) (o + q)) _ _ _ H27b) in Hc1 by reflexivity.
      pose proof (pl_cls_bit0 _ Hcr Hnal Hc0 Hc1) as Hnp.
      aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan PL_N; [pl_awr U2|].
lazymatch type of HFr1 with frame_of ?Ex ?rs _ _ =>
  assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
  assert (KE3 : pl_same cx W3 (ms_mem ms0) (ms_mem ms1)) by
    (intros a Ha Hn; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha);
     intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
     destruct Hin as [<-|[<-|[<-|[]]]];
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr;
       apply Hn; unfold pl_win; lia);
  clear X2 end.
      assert (KE : pl_same cx W3 mem3 (ms_mem ms1)) by exact (pl_same_trans cx W3 _ _ _ KEa KE3).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRrp;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
  cbn [ms_mem restrict] in HRrp, HRd end.
assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms1)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
{ replace (cx_sp cx) with (cx_F cx + 208) by lia.
  apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 208 8%N (SOff 34 0) (cx_v cx + Z.of_nat d) HRrp
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E34, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (Vd : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms1)) (cx_F cx + 8) 8 (Z.of_nat d)).
{ apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 8 8%N (SOff 35 0) (Z.of_nat d) HRd
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_KEPT2 HS
  ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
assert (HPRpl : pl_regs_pl regs3 (ms_regs ms1)).
{ apply pl_regs_pl_of_kept; [exact KR | |].
  - rreg HS (20%bv : bv 5) Q20. rewrite Q20, R20. cbn [sv_denot ew ewset Nat.eqb].
    rewrite U2. unfold w64. f_equal. lia.
  - rreg HS (25%bv : bv 5) Q25. rewrite Q25, R25. cbn [ew ewset Nat.eqb]. exact E21. }
assert (R27x : getr (ms_regs ms1) 27 = w64 (byte_at (cx_ub cx) (o + q)))
  by (rewrite (KR 27%bv ltac:(pl_in)); exact R27).
pose proof (pl_PL_kept cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 (ms_regs ms1) (ms_mem ms1) _
  (cx_F cx) HPL0 HJ ltac:(lia) ltac:(lia) HFlo HFhi KE HPRpl Vrp Vd) as HPLx.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
exact (pl_from_N f cx i d s11 p1 p2 p3 o q ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ HSEGL HB HPLx R27x Hnp).
    }
    { (* bit set: plain *)
      erewrite (pl_D_of 27 _ (byte_at (cx_ub cx) (o + q)) _ _ _ H27b) in Hc1 by reflexivity.
      pose proof (pl_cls_bit1 _ Hcr Hnal Hc0 Hc1) as Hpl.
      aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan PL_P; [pl_awr U2|].
lazymatch type of HFr1 with frame_of ?Ex ?rs _ _ =>
  assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
  assert (KE3 : pl_same cx W3 (ms_mem ms0) (ms_mem ms1)) by
    (intros a Ha Hn; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha);
     intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
     destruct Hin as [<-|[<-|[<-|[]]]];
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr;
       apply Hn; unfold pl_win; lia);
  clear X2 end.
      assert (KE : pl_same cx W3 mem3 (ms_mem ms1)) by exact (pl_same_trans cx W3 _ _ _ KEa KE3).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRrp;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRd;
  cbn [ms_mem restrict] in HRrp, HRd end.
assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms1)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
{ replace (cx_sp cx) with (cx_F cx + 208) by lia.
  apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 208 8%N (SOff 34 0) (cx_v cx + Z.of_nat d) HRrp
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E34, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (Vd : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms1)) (cx_F cx + 8) 8 (Z.of_nat d)).
{ apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 8 8%N (SOff 35 0) (Z.of_nat d) HRd
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, unsigned_lit_small by lia; unfold w64; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_KEPT2 HS
  ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
assert (HPRpl : pl_regs_pl regs3 (ms_regs ms1)).
{ apply pl_regs_pl_of_kept; [exact KR | |].
  - rreg HS (20%bv : bv 5) Q20. rewrite Q20, R20. cbn [sv_denot ew ewset Nat.eqb].
    rewrite U2. unfold w64. f_equal. lia.
  - rreg HS (25%bv : bv 5) Q25. rewrite Q25, R25. cbn [ew ewset Nat.eqb]. exact E21. }
assert (R27x : getr (ms_regs ms1) 27 = w64 (byte_at (cx_ub cx) (o + q)))
  by (rewrite (KR 27%bv ltac:(pl_in)); exact R27).
pose proof (pl_PL_kept cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 (ms_regs ms1) (ms_mem ms1) _
  (cx_F cx) HPL0 HJ ltac:(lia) ltac:(lia) HFlo HFhi KE HPRpl Vrp Vd) as HPLx.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
exact (pl_from_P f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ HSEGL HSEGPL Hm HB HPLx R27x Hpl).
    } } }
Qed.

(* ======== the segment: from plain_local's head, local[q] ======== *)
Theorem rd_PL_holds : forall f m, rd_seg_L B CTX f -> rd_seg_PL B CTX (S f) m -> rd_seg_PL B CTX (S f) (S m).
Proof using IMG ISALNUM HASP.
intros f m HSEGL HSEGPL cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 Hm HB HPL.
pose proof HPL as HPL0.
pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs. pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (CC & _).
unfold rd_PL in HPL. cbv zeta in HPL.
destruct HPL as (HLOOP & HACC & Hilt & HDECL & HFI & Ho & HFirst & HLast & Hqn & HPlainq & HS38 & R19 & R20 &
  R21 & R22 & R23 & R24 & R25 & R26).
pose proof HLOOP as HMID.
pose proof HMID as (HCOM & R9 & R18 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof HCOM as (HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HB as (HAN & HCTX & HROb & H10b & H11b & H12b & Hpresb & Htopr & Hvb & Hv63 & Ctb & Cub & Ktb & Kub &
  Hub255 & Htbmax & HGb & Hlv & Hcntb & Hevb & Hlbb).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARj & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (HSP : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (HFlo : alloc_ceiling + 4096 <= cx_F cx) by lia.
assert (HFhi : cx_sp cx + 16 <= 2 ^ 47) by lia.
assert (HF16 : cx_F cx mod 16 = 0) by
  (rewrite HFsp; replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia; rewrite Z_mod_plus_full;
   rewrite HSP; exact Hal16).
pose proof Ct as ((_ & _) & Ht1 & Ht2 & _).
pose proof Cu as ((HGu & HNZu) & Hu1 & Hu2 & _).
assert (Hclose : (S p3 + o < length (cx_tb cx))%nat) by
  (pose proof (pl_find_idx_lt _ _ _ HFI) as Hlt; rewrite length_skipn in Hlt; lia).
assert (Hoq : (o + q < length (cx_ub cx))%nat) by lia.
unfold rd_slots_ok in HSLOTS. rewrite pl_loc_list in HSLOTS.
apply Forall_cons_iff in HSLOTS as [SL0 HSLOTS]. apply Forall_cons_iff in HSLOTS as [SL8 HSLOTS].
cbv [pl_rest] in HSLOTS.
apply Forall_cons_iff in HSLOTS as [SL18 HSLOTS]. apply Forall_cons_iff in HSLOTS as [SL20 HSLOTS].
apply Forall_cons_iff in HSLOTS as [SL30 HSLOTS]. apply Forall_cons_iff in HSLOTS as [SL40 HSLOTS].
cbn [fst snd] in SL0, SL8, SL18, SL20, SL30, SL40.
pose proof HS38 as HS38'.
unfold rd_slots_ok in HS38'. apply Forall_cons_iff in HS38' as [SL38 _]. cbn [fst snd] in SL38.
destruct (HGu (o + q)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
rewrite app_nth1 in Vc, Rc by lia.
pose proof Cu as (_ & _ & _ & _ & _ & HRAu & _).
assert (Vc' : val_mem tfibsegs (mrestrict (w_H W3) mem3) (cx_u cx + Z.of_nat o + Z.of_nat q) 1
  (byte_at (cx_ub cx) (o + q))) by (rewrite <- Z.add_assoc, <- Nat2Z.inj_add; exact Vc).
pose proof (plA_entry W3 regs3 mem3 (cx_F cx) (cx_u cx + Z.of_nat o + Z.of_nat q) (byte_at (cx_ub cx) (o + q))
  R2 R8 ltac:(rewrite R20; unfold w64; f_equal; lia) R21 R25 ltac:(lia) HF16 ltac:(lia)
  ltac:(unfold byte_at; lia) Vc') as HS.
set (E := Ereg regs3 [w64 (byte_at (cx_ub cx) (o + q))]) in *.
assert (E2a : ew E 2 = getr regs3 2) by (unfold E; exact (ew_Ereg_nat regs3 _ 2 2%bv eq_refl)).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite E2a, R2; apply unsigned_lit_small; lia).
assert (E3a : ew E 3 = getr regs3 3) by (unfold E; exact (ew_Ereg_nat regs3 _ 3 3%bv eq_refl)).
assert (E4a : ew E 4 = getr regs3 4) by (unfold E; exact (ew_Ereg_nat regs3 _ 4 4%bv eq_refl)).
assert (E8a : ew E 8 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl); exact R8).
assert (E21 : ew E 21 = w64 (cx_u cx + Z.of_nat o + Z.of_nat q))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 21 21%bv eq_refl); exact R21).
assert (E32 : ew E 32 = w64 (byte_at (cx_ub cx) (o + q))) by (unfold E; exact (ew_Ereg_extra regs3 _ 0)).
assert (SHOK : sh_ok tfibsegs PL_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 PL_A) mem3 (seg_rom tfibsegs))))) by constructor.
change (unpoison [] mem3) with mem3 in HJ.
unfold cfg_at. change (w64 0x81fc8) with (Z_to_bv 64 PL_A).
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 PL_A) mem3 (seg_rom tfibsegs))) in HJ.
(* the shadow check of local + q, the byte, isalnum *)
aj_run_tok rd_tbl_ok HS HJ SHOK PL_Bspan; [ | pl_awr U2 | ].
{ apply (obl_of_range tfibsegs (w_H W3) mem3 E PL_Bx (U E (SOff 21 0)) 1 (cx_u cx)
    (Z.of_nat (length (cx_ub cx)) + 1) HRAu).
  - unfold PL_Bx. apply (U_atom E 8 SHADOW_OFF E8a). unfold SHADOW_OFF. lia.
  - rewrite (U_atom E 21 _ E21 ltac:(lia)). lia.
  - rewrite (U_atom E 21 _ E21 ltac:(lia)). lia. }
lazymatch goal with H : frame_of E (ss_mem ss_A) mem3 _ |- _ =>
  pose proof (frame_of_read_only E (ss_mem ss_A) _ _ eq_refl H) as Hm0 end.
rreg HS (1%bv : bv 5) Qra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp.
rreg HS (10%bv : bv 5) Qa0. rreg HS (20%bv : bv 5) Q20. rreg HS (25%bv : bv 5) Q25. rreg HS (27%bv : bv 5) Q27.
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_KEPT4 HS
  ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
assert (HPRa : pl_regs_pl regs3 (ms_regs ms)).
{ apply pl_regs_pl_of_kept4; [exact KR | |].
  - rewrite Q20, R20. cbn [sv_denot ew ewset Nat.eqb]. rewrite U2. unfold w64. f_equal. lia.
  - rewrite Q25, R25. cbn [ew ewset Nat.eqb]. exact E21. }
assert (Hsp1 : spZ (ms_regs ms) = cx_sp cx + 16 + (-224))
  by (unfold spZ; rewrite Qsp; cbn [ew ewset Nat.eqb]; rewrite U2; lia).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ eapply (g3_aj_ro_at B LAWS PC_isalnum STK_RT_ISALNUM
    (fun v => v <> 0 <-> is_alnum (byte_at (cx_ub cx) (o + q)) = true)
    W3 (ms_regs ms) (ms_mem ms) (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx)
    (cx_mem cx) (cx_md cx) [] ly3 S3 _ EV_names (-224) (Z_to_bv 64 0x81fe4) HJ).
  - exact Hsp1.
  - reflexivity.
  - lia.
  - unfold STK_RT_ISALNUM. lia.
  - unfold STK_RT_ISALNUM, ESTACK. lia.
  - rewrite Qgp. cbn [ew ewset Nat.eqb]. rewrite E3a, R3. exact Hgp.
  - rewrite Qtp. cbn [ew ewset Nat.eqb]. rewrite E4a, R4. exact Htp.
  - exact Qra.
  - vm_compute. reflexivity.
  - intros HPK. apply (ISALNUM ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ (byte_at (cx_ub cx) (o + q)) HPK).
    + rewrite Qa0. cbn [ew ewset Nat.eqb]. exact E32.
    + unfold byte_at. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & vv & -> & HJ2 & HP2 & H10v & Hvv & HR & Hfr2 & Hpres2).
assert (HPR2 : pl_regs_pl regs3 regs2) by exact (pl_regs_pl_trans _ _ _ HPRa (pl_regs_pl_of_pres _ _ HP2)).
assert (KEt : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - 4096 <= a < cx_F cx) ->
  aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha Hn. rewrite <- Hm0. apply Hfr2; [exact Ha|]. unfold STK_RT_ISALNUM, ESTACK. intros Hw.
  apply Hn. lia. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ pl_win cx (cx_F cx - 4096) a ->
  aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) mem3 a)
  by (intros a Ha Hn; apply KEt; [exact Ha | unfold pl_win in Hn; lia]).
assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) mem2) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
{ apply (g3_val_mem_kept W3 W3 mem3 mem2); [exact HRP|]. intros j Hj. cbn in Hj. apply KEt; lia. }
assert (Vd : val_mem tfibsegs (mrestrict (w_H W3) mem2) (cx_F cx + 8) 8 (Z.of_nat d)).
{ apply (g3_val_mem_kept W3 W3 mem3 mem2); [exact (proj1 SL8)|]. intros j Hj. cbn in Hj. apply KEt; lia. }
pose proof (pl_PL_kept cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 regs2 mem2 md2
  (cx_F cx - 4096) HPL0 HJ2 ltac:(lia) ltac:(lia) HFlo HFhi KE HPR2 Vrp Vd) as HPL2.
assert (R27b : getr regs2 27 = w64 (byte_at (cx_ub cx) (o + q))).
{ assert (Q27b : getr regs2 27 = getr (ms_regs ms) 27) by exact (HP2 27 ltac:(unfold acallee_saved; lia)).
  rewrite Q27b, Q27. cbn [ew ewset Nat.eqb]. exact E32. }
exact (pl_from_B f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs2 mem2 md2 vv HSEGL HSEGPL ltac:(lia) HB HPL2 R27b
  H10v Hvv HR).
Qed.

End c.
