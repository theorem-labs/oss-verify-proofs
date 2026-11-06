(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AF0x.v, with its module paths and module names changed; 571 of its 675 lines of code are new or changed and 468 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/B/FMW_rd_pre_k.v; 1663 of its 1843 lines of code are new or changed and 495 lines of the source are left out. *)
(* lv2_locate_manifest_readings on fm.asan-ubsan (image B, pin ca61e5c9eabc0050): plain_local's loop at 0x8227c
   (lv2_locate.c:48-51, 139-145), the segment statement rd_seg_PL of lib/B/FMW_rd_cuts.v: rd_PL_holds (FMW_rd_top.v's
   SEG_PL). A re-walk of A's lib/A/FMW_rd_pl.v (a working branch e2e59892bef) on B's code: B counts q up in s8
   against n in a3 and keeps read_again in s1, local's bases in the frame (F+0x08 / 0x30 / 0x38, ~local at F+0x40).
   The walk, cut at seven pcs, each with its own symbolic state built from Props:
     A  0x8227c (rd_PL): ~local <u q is the UBSan guard 0x82280 (refuted by the facts: ~local >= 2^64 - 2^47 > q),
        s9 = n, the shadow check of local + q (F+0x38 + q), a0 = F+0x30 + q; the run stops at the load 0x822a8;
     A2 0x822a8 (pl_from_A2): c = ub[o + q] (s10), isalnum (PC_isalnum, ra 0x822b4);
     B  0x822b4 (pl_from_B, RD_C11): a3 = s9, isalnum's answer, then c - 45 >u 50 and bit (c - 45) of RD_MASK2
        (pl_cls_*, decided over all 256 bytes) -> P or N;
     P  0x822d8 (pl_from_P): s8 = q + 1; q + 1 <> n -> back to A at q + 1 (rd_seg_PL); else s8 = addiw (s1, 1) = d + 1,
        the UBSan guard 0x822f4 (d + 1 <s d, refuted: d <= 16), s9 = 1, 16 <s d + 1 -> RD_R (readings_scan sc_cnt),
        else ++*readings (the 8-byte check of rp = F+0x10 from the stack's zero shadow) and has_prefixed (0x823e4,
        ra 0x82338) -> C;
     N  0x81ffc (pl_from_N, RD_CONT): the name is not plain, the declaration does not match -> RD_L at S close
        (sc_nomatch); the guard 0x8200c (close = -1, j 0x823b4) refuted by the facts (close < 2^47);
     C  0x82338 (pl_from_C, RD_C12): has_prefixed's answer: a token -> RD_R (sc_tok), else RD_CONT2 0x82000 with
        s8 = d + 1 -> RD_L (sc_next), the guard 0x8200c refuted as at N.
   Memory across a step: pl_win / pl_same (only the callees' stacks and *readings change), pl_com_kept /
   pl_mid_kept / pl_core_kept; across has_prefixed: pl_mid_hp (its journal, fm_img_facts for the strings). The pure
   model steps are copies of lib/Prog/readings_scan.v:177-310 (that file imports lib/Lib). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YG0s YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_cuts FMW_rd_ret.
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


(* ======== the byte classification: isalnum, then c - 45 >u 50, then bit (c - 45) of RD_MASK2 (c in s10 = x26) ======== *)
Definition pl_b1 : sv := SOff 26 (-45).
Definition pl_b2 : sv := SAlu ALU_AND (SAlu ALU_SRL (SLit RD_MASK2) (SOff 26 (-45))) (SLit 1).
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

Definition pl_cls_ok (c : Z) : bool :=
  let d1 := pl_D 26 BC_LTU (SLit 50) pl_b1 c in
  let d2 := pl_D 26 BC_EQ pl_b2 (SLit 0) c in
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
  pl_D 26 BC_LTU (SLit 50) pl_b1 c = true -> plain_ok c = false.
Proof. intros c Hc. pl_cls_tac c Hc. Qed.
Lemma pl_cls_bit0 : forall c, 0 <= c < 256 -> is_alnum c = false ->
  pl_D 26 BC_LTU (SLit 50) pl_b1 c = false -> pl_D 26 BC_EQ pl_b2 (SLit 0) c = true -> plain_ok c = false.
Proof. intros c Hc. pl_cls_tac c Hc. Qed.
Lemma pl_cls_bit1 : forall c, 0 <= c < 256 -> is_alnum c = false ->
  pl_D 26 BC_LTU (SLit 50) pl_b1 c = false -> pl_D 26 BC_EQ pl_b2 (SLit 0) c = false -> plain_ok c = true.
Proof. intros c Hc. pl_cls_tac c Hc. Qed.

(* ======== the cut states ======== *)
Definition PL_A : Z := 0x8227c.   (* plain_local's head (RD_PL) *)
Definition PL_A2 : Z := 0x822a8.  (* the load of local[q], after the shadow check *)
Definition PL_B : Z := 0x822b4.   (* after isalnum (RD_C11) *)
Definition PL_P : Z := 0x822d8.   (* the byte is plain *)
Definition PL_N : Z := 0x81ffc.   (* the byte is not plain: RD_CONT *)
Definition PL_C : Z := 0x82338.   (* after has_prefixed (RD_C12) *)
Definition PL_Bx : sv := SOff 27 0.                                 (* s11 = the shadow base *)
Definition PL_Bspan : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).

(* A 0x8227c: atom 2 = F, 27 = the shadow base, 24 = q, 32 = local, 33 = ~local; the frame slots 0x30 / 0x38
   (local) and 0x40 (~local), read only. The UBSan guard 0x82280 (bltu ~local, q) falls by the atom ranges. *)
Definition pl_facts_A : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47 - 224) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (24%nat, mkAF 0 254 0); (32%nat, mkAF 4096 (2 ^ 47 - 4096) 0);
           (33%nat, mkAF (2 ^ 64 - 2 ^ 47 + 4095) (2 ^ 64 - 4097) 0)] [] [].
Definition pl_frA : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x30 0x48 0 0
    [YP09.mkChunk 0x30 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x38 (CVal 8 (SOff 32 0));
     YP09.mkChunk 0x40 (CVal 8 (SOff 33 0))].
Definition ss_A : sstate := mkSS PL_A sr_atoms [pl_frA] None pl_facts_A.

(* A2 0x822a8: atom 10 = local + q (a0), 32 = the byte *)
Definition pl_facts_A2 : facts :=
  mkFacts [(10%nat, mkAF 4096 (2 ^ 47) 0); (32%nat, mkAF 0 255 0)] [] [].
Definition pl_byte : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition ss_A2 : sstate := mkSS PL_A2 sr_atoms [pl_byte] None pl_facts_A2.

(* B 0x822b4: atom 2 = F, 26 = the byte (s10); the mask slot F+0x18, read only. a3 is dead here (isalnum's
   clobber), s9 = n is moved into it by the first instruction. *)
Definition pl_facts_B : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47 - 224) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (26%nat, mkAF 0 255 0)] [] [].
Definition pl_fr_mask : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x18 0x20 0 0 [YP09.mkChunk 0x18 (CVal 8 (SLit RD_MASK2))].
Definition ss_B : sstate := mkSS PL_B sr_atoms [pl_fr_mask] None pl_facts_B.

(* P 0x822d8: atom 9 = d (s1), 13 = n (a3), 24 = q (s8), 32 = local, 33 = text, 34 = the name's length,
   35 = *readings; the frame slots 0x08 (local), 0x10 (rp = F + 208), 0x48, 0x50, read only, and the counter cell
   at F + 208, writable. The UBSan guard 0x822f4 (blt d + 1, d) falls by atom 9's offsets. *)
Definition pl_facts_P : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47 - 224) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (9%nat, mkAF 0 16 0); (13%nat, mkAF 1 255 0); (24%nat, mkAF 0 254 0)] [] [].
Definition pl_fr_P : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x08 0x58 0 0
    [YP09.mkChunk 0x08 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x10 (CVal 8 (SOff 2 208));
     YP09.mkChunk 0x48 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x50 (CVal 8 (SOff 33 0))].
Definition pl_fr_rp : YP09.region :=
  YP09.mkRegion (Some 2%nat) 208 216 208 216 [YP09.mkChunk 208 (CVal 8 (SOff 35 0))].
Definition ss_P : sstate := mkSS PL_P sr_atoms [pl_fr_P; pl_fr_rp] None pl_facts_P.

(* N 0x81ffc (RD_CONT) and C 0x82338 (RD_C12): only registers. atom 8 = -1 and 21 = close refute the guard
   0x8200c / 0x82010 (bne close, -1 else j 0x823b4); atom 24 = d + 1 at C. *)
Definition pl_facts_N : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47 - 224) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (8%nat, mkAF RD_M1 RD_M1 0); (21%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition ss_N : sstate := mkSS PL_N sr_atoms [] None pl_facts_N.
Definition pl_facts_C : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47 - 224) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (8%nat, mkAF RD_M1 RD_M1 0); (21%nat, mkAF 4096 (2 ^ 47) 0); (24%nat, mkAF 1 17 0)] [] [].
Definition ss_C : sstate := mkSS PL_C sr_atoms [] None pl_facts_C.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

Lemma pl_chunk8 : forall E m b off (e : sv) v,
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs m (b + off) 8 v ->
  YP09.chunk_ok tfibsegs E m b (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros E m b off e v He Hv Hm. apply (chunk_ok_val tfibsegs E m b off 8%N e v He); [cbn; lia | cbn; lia | exact Hm].
Qed.

(* the shadow check's address: a0 = local + q is the sum of two atoms (A's a0 was one register) *)
Lemma pl_U_add : forall E n m x y,
  ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= x + y < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = x + y.
Proof.
  intros E n m x y Hn Hm Hx Hy Hxy. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E n x Hn Hx), (U_atom E m y Hm Hy). apply zcanon_id. unfold M64. lia.
Qed.

(* A 0x8227c *)
Lemma plA_entry : forall (W : world tfibsegs) regs mem F qv localv,
  getr regs 2 = w64 F -> getr regs 27 = w64 SHADOW_OFF -> getr regs 24 = w64 qv ->
  2 ^ 46 <= F <= 2 ^ 47 - 224 -> F mod 16 = 0 -> 0 <= qv <= 254 -> 4096 <= localv <= 2 ^ 47 - 4096 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 0x30) 8 localv ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 0x38) 8 localv ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 0x40) 8 (RD_M1 - localv) ->
  st_ok tfibsegs (Ereg regs [w64 localv; w64 (RD_M1 - localv)]) ss_A
    (restrict (w_H W) (mkst regs (Z_to_bv 64 PL_A) mem (seg_rom tfibsegs))).
Proof.
  intros W regs mem F qv localv R2 R27 R24 HF HF16 Hq Hl V30 V38 V40.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs [w64 localv; w64 (RD_M1 - localv)]).
  assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
  assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
  assert (E24 : ew E 24 = w64 qv) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (E32 : ew E 32 = w64 localv) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = w64 (RD_M1 - localv)) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
  assert (U2 : bv_unsigned (ew E 2) = F) by (rewrite E2; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF) by (rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U24 : bv_unsigned (ew E 24) = qv) by (rewrite E24; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = localv) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = RD_M1 - localv)
    by (rewrite E33; apply unsigned_lit_small; unfold RD_M1; lia).
  unfold ss_A. apply (entry_st_ok_full tfibsegs); change (Ereg regs [w64 localv; w64 (RD_M1 - localv)]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold pl_frA, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (pl_chunk8 E _ F 0x30 (SOff 32 0) localv);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | lia | exact V30].
    + apply (pl_chunk8 E _ F 0x38 (SOff 32 0) localv);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | lia | exact V38].
    + apply (pl_chunk8 E _ F 0x40 (SOff 33 0) (RD_M1 - localv));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | unfold RD_M1; lia | exact V40].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pl_facts_A]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U27, U24, U32, U33. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, RD_M1. repeat split; try lia.
Qed.

(* A2 0x822a8 *)
Lemma plA2_entry : forall (W : world tfibsegs) regs mem lq c,
  getr regs 10 = w64 lq -> 4096 <= lq <= 2 ^ 47 -> 0 <= c < 256 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) lq 1 c ->
  st_ok tfibsegs (Ereg regs [w64 c]) ss_A2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 PL_A2) mem (seg_rom tfibsegs))).
Proof.
  intros W regs mem lq c R10 Hlq Hc Vc.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs [w64 c]).
  assert (E10 : ew E 10 = w64 lq) by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
  assert (E32 : ew E 32 = w64 c) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
  assert (U10 : bv_unsigned (ew E 10) = lq) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
  unfold ss_A2. apply (entry_st_ok_full tfibsegs); change (Ereg regs [w64 c]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold pl_byte, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
    split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs E _ lq 0 1%N (SOff 32 0) c);
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Vc.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pl_facts_A2]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U32. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; try lia.
Qed.

(* B 0x822b4 *)
Lemma plB_entry : forall (W : world tfibsegs) regs mem F c,
  getr regs 2 = w64 F -> getr regs 27 = w64 SHADOW_OFF -> getr regs 26 = w64 c ->
  2 ^ 46 <= F <= 2 ^ 47 - 224 -> F mod 16 = 0 -> 0 <= c < 256 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 0x18) 8 RD_MASK2 ->
  st_ok tfibsegs (Ereg regs []) ss_B (restrict (w_H W) (mkst regs (Z_to_bv 64 PL_B) mem (seg_rom tfibsegs))).
Proof.
  intros W regs mem F c R2 R27 R26 HF HF16 Hc V18.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs ([] : list word)).
  assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
  assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
  assert (E26 : ew E 26 = w64 c) by (unfold E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  assert (U2 : bv_unsigned (ew E 2) = F) by (rewrite E2; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF) by (rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U26 : bv_unsigned (ew E 26) = c) by (rewrite E26; apply unsigned_lit_small; lia).
  unfold ss_B. apply (entry_st_ok_full tfibsegs); change (Ereg regs ([] : list word)) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold pl_fr_mask, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (pl_chunk8 E _ F 0x18 (SLit RD_MASK2) RD_MASK2); [reflexivity | unfold RD_MASK2; lia | exact V18].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pl_facts_B]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U27, U26. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; try lia.
Qed.

(* P 0x822d8 *)
Lemma plP_entry : forall (W : world tfibsegs) regs mem F dv nv qv localv textv namelen rpv,
  getr regs 2 = w64 F -> getr regs 27 = w64 SHADOW_OFF ->
  getr regs 9 = w64 dv -> getr regs 13 = w64 nv -> getr regs 24 = w64 qv ->
  2 ^ 46 <= F <= 2 ^ 47 - 224 -> F mod 16 = 0 -> 0 <= dv <= 16 -> 1 <= nv <= 255 -> 0 <= qv <= 254 ->
  0 <= localv < 2 ^ 64 -> 0 <= textv < 2 ^ 64 -> 0 <= namelen < 2 ^ 64 -> 0 <= rpv < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 0x08) 8 localv ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 0x10) 8 (F + 208) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 0x48) 8 namelen ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 0x50) 8 textv ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 208) 8 rpv ->
  (forall a, F + 208 <= a < F + 216 -> writable_at tfibsegs (mrestrict (w_H W) mem) a) ->
  st_ok tfibsegs (Ereg regs [w64 localv; w64 textv; w64 namelen; w64 rpv]) ss_P
    (restrict (w_H W) (mkst regs (Z_to_bv 64 PL_P) mem (seg_rom tfibsegs))).
Proof.
  intros W regs mem F dv nv qv localv textv namelen rpv R2 R27 R9 R13 R24
    HF HF16 Hd Hn Hq Hlocal Htext Hname Hrp V08 V10 V48 V50 V208 W208.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs [w64 localv; w64 textv; w64 namelen; w64 rpv]).
  assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
  assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
  assert (E9 : ew E 9 = w64 dv) by (unfold E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (E13 : ew E 13 = w64 nv) by (unfold E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact R13).
  assert (E24 : ew E 24 = w64 qv) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (E32 : ew E 32 = w64 localv) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = w64 textv) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = w64 namelen) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = w64 rpv) by (unfold E; exact (ew_Ereg_extra regs _ 3)).
  assert (U2 : bv_unsigned (ew E 2) = F) by (rewrite E2; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF) by (rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U9 : bv_unsigned (ew E 9) = dv) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U13 : bv_unsigned (ew E 13) = nv) by (rewrite E13; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = qv) by (rewrite E24; apply unsigned_lit_small; lia).
  unfold ss_P. apply (entry_st_ok_full tfibsegs);
    change (Ereg regs [w64 localv; w64 textv; w64 namelen; w64 rpv]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold pl_fr_P, pl_fr_rp.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U2.
    + split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (pl_chunk8 E _ F 0x08 (SOff 32 0) localv);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
          | lia | exact V08].
      * apply (pl_chunk8 E _ F 0x10 (SOff 2 208) (F + 208));
          [cbn [sv_denot]; rewrite E2, unsigned_lit_small by lia; reflexivity | lia | exact V10].
      * apply (pl_chunk8 E _ F 0x48 (SOff 34 0) namelen);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
          | lia | exact V48].
      * apply (pl_chunk8 E _ F 0x50 (SOff 33 0) textv);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
          | lia | exact V50].
    + split; [lia|]. split; [lia|]. split; [intros oo Hoo; apply W208; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (pl_chunk8 E _ F 208 (SOff 35 0) rpv);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | lia | exact V208].
  - apply pairwise_disjoint_of_extents. unfold pl_fr_P, pl_fr_rp, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pl_facts_P]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U27, U9, U13, U24. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; try lia.
Qed.

(* N 0x81ffc and C 0x82338: registers only *)
Lemma plN_entry : forall (W : world tfibsegs) regs mem F closev,
  getr regs 2 = w64 F -> getr regs 27 = w64 SHADOW_OFF -> getr regs 8 = w64 RD_M1 -> getr regs 21 = w64 closev ->
  2 ^ 46 <= F <= 2 ^ 47 - 224 -> F mod 16 = 0 -> 4096 <= closev <= 2 ^ 47 ->
  st_ok tfibsegs (Ereg regs []) ss_N (restrict (w_H W) (mkst regs (Z_to_bv 64 PL_N) mem (seg_rom tfibsegs))).
Proof.
  intros W regs mem F closev R2 R27 R8 R21 HF HF16 Hc.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs ([] : list word)).
  assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
  assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
  assert (E8 : ew E 8 = w64 RD_M1) by (unfold E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
  assert (E21 : ew E 21 = w64 closev) by (unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
  assert (U2 : bv_unsigned (ew E 2) = F) by (rewrite E2; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF) by (rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U8 : bv_unsigned (ew E 8) = RD_M1) by (rewrite E8; apply unsigned_lit_small; unfold RD_M1; lia).
  assert (U21 : bv_unsigned (ew E 21) = closev) by (rewrite E21; apply unsigned_lit_small; lia).
  unfold ss_N. apply (entry_st_ok_full tfibsegs); change (Ereg regs ([] : list word)) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pl_facts_N]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U27, U8, U21. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, RD_M1. repeat split; try lia.
Qed.

Lemma plC_entry : forall (W : world tfibsegs) regs mem F closev dv,
  getr regs 2 = w64 F -> getr regs 27 = w64 SHADOW_OFF -> getr regs 8 = w64 RD_M1 ->
  getr regs 21 = w64 closev -> getr regs 24 = w64 dv ->
  2 ^ 46 <= F <= 2 ^ 47 - 224 -> F mod 16 = 0 -> 4096 <= closev <= 2 ^ 47 -> 1 <= dv <= 17 ->
  st_ok tfibsegs (Ereg regs []) ss_C (restrict (w_H W) (mkst regs (Z_to_bv 64 PL_C) mem (seg_rom tfibsegs))).
Proof.
  intros W regs mem F closev dv R2 R27 R8 R21 R24 HF HF16 Hc Hd.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs ([] : list word)).
  assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
  assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
  assert (E8 : ew E 8 = w64 RD_M1) by (unfold E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
  assert (E21 : ew E 21 = w64 closev) by (unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
  assert (E24 : ew E 24 = w64 dv) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (U2 : bv_unsigned (ew E 2) = F) by (rewrite E2; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF) by (rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U8 : bv_unsigned (ew E 8) = RD_M1) by (rewrite E8; apply unsigned_lit_small; unfold RD_M1; lia).
  assert (U21 : bv_unsigned (ew E 21) = closev) by (rewrite E21; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = dv) by (rewrite E24; apply unsigned_lit_small; lia).
  unfold ss_C. apply (entry_st_ok_full tfibsegs); change (Ereg regs ([] : list word)) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pl_facts_C]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U27, U8, U21, U24. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, RD_M1. repeat split; try lia.
Qed.

End e.
(* ======== the memory a callee keeps (local copies of G5's FMW_kitS and G6's FMW_kit lemmas, restated here so the
   segment builds on G3's kit alone) ======== *)
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

(* ---- what the loop's invariant needs of the memory a step changes: on B only the callees' stacks (below F) and
   the counter cell *readings = [sp, sp + 8) are written ---- *)
Definition pl_win (cx : rdcx) (lo a : Z) : Prop :=
  (lo <= a < cx_F cx) \/ (cx_sp cx <= a < cx_sp cx + 8).

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

(* the registers a step keeps: rd_com's (PL_COM), the scan's constants (PL_LOOP, read_again x9 apart) and the
   plain_local cut's (PL_CORE) *)
Definition pl_keeps (L : list (bv 5)) (regs regs' : bvmap 5 word) : Prop :=
  forall r, In r L -> getr regs' r = getr regs r.
Definition PL_COM : list (bv 5) := [2; 3; 4; 27]%bv.
Definition PL_LOOP : list (bv 5) := [2; 3; 4; 8; 18; 19; 20; 23; 27]%bv.
Definition PL_CORE : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 27]%bv.
(* everything the plain_local cut needs but s8 = q, which the back edge raises to q + 1 *)
Definition PL_KEEP1 : list (bv 5) := [2; 3; 4; 8; 9; 13; 18; 19; 20; 21; 22; 23; 27]%bv.
(* the same without a3 = n, which the call to has_prefixed takes as its argument *)
Definition PL_KEEP2 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 27]%bv.

Ltac pl_sub := intros rr Hrr; cbv [PL_COM PL_LOOP PL_CORE PL_KEEP1 PL_KEEP2 G3_KEPT In] in Hrr |- *;
  repeat (destruct Hrr as [<-|Hrr]; [repeat (first [left; reflexivity | right])|]); destruct Hrr.

Lemma pl_keeps_sub : forall L1 L2 regs regs',
  (forall r, In r L1 -> In r L2) -> pl_keeps L2 regs regs' -> pl_keeps L1 regs regs'.
Proof. intros L1 L2 regs regs' Hs H r Hr. exact (H r (Hs r Hr)). Qed.

Lemma pl_keeps_trans : forall L r1 r2 r3, pl_keeps L r1 r2 -> pl_keeps L r2 r3 -> pl_keeps L r1 r3.
Proof. intros L r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma pl_keeps_of_pres : forall L regs regs', aregs_preserved regs regs' ->
  (forall r, In r L -> In r (2%bv :: G3_KEPT)) -> pl_keeps L regs regs'.
Proof.
intros L regs regs' HP Hsub r Hr. destruct (Hsub r Hr) as [<-|Hin].
- exact (HP 2 ltac:(unfold acallee_saved; lia)).
- exact (g3_aregs_keep regs regs' HP r Hin).
Qed.

Lemma pl_com_kept : forall cx k ly3 S3 (W3 : world tfibsegs) regs3 mem3 md3 regsB memB mdB lo,
  rd_com B cx k [] ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 memB mdB k ->
  alloc_ceiling <= lo -> lo <= cx_F cx -> alloc_ceiling + 4096 <= cx_F cx -> cx_sp cx + 16 <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pl_win cx lo a -> aview tfibsegs (w_H W3) memB a = aview tfibsegs (w_H W3) mem3 a) ->
  pl_keeps PL_COM regs3 regsB ->
  rd_com B cx k [] ly3 S3 W3 regsB memB mdB.
Proof.
intros cx k ly3 S3 W3 regs3 mem3 md3 regsB memB mdB lo HCOM HJ Hlo HloF HFlo HFhi HAV HP.
pose proof HCOM as (HJ0 & Hk & R2 & R3 & R4 & R27 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof asan_consts as (CC & _).
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (KL : g3_low_kept W3 W3 mem3 memB).
{ intros a Ha. apply HAV; [lia|]. unfold pl_win. lia. }
split; [change (unpoison [] memB) with memB; exact HJ|]. split; [exact Hk|].
split; [rewrite (HP 2%bv ltac:(cbv [PL_COM In]; tauto)); exact R2|].
split; [rewrite (HP 3%bv ltac:(cbv [PL_COM In]; tauto)); exact R3|].
split; [rewrite (HP 4%bv ltac:(cbv [PL_COM In]; tauto)); exact R4|].
split; [rewrite (HP 27%bv ltac:(cbv [PL_COM In]; tauto)); exact R27|].
split.
{ apply (pl_saved_kept cx W3 W3 mem3 memB HSV). intros a Ha. apply HAV; [lia|]. unfold pl_win. lia. }
split.
{ intros a Ha. rewrite (HAV a ltac:(lia) ltac:(unfold pl_win; lia)). exact (K16 a Ha). }
split; [exact (g3_arodata_kept B W3 W3 mem3 memB HRO KL)|].
split; [exact (g3_cstr_ok_kept W3 W3 mem3 memB _ _ Ct KL)|].
split; [exact (g3_cstr_ok_kept W3 W3 mem3 memB _ _ Cu KL)|].
split; [exact Kt | exact Ku].
Qed.

(* the loop's invariant with *readings read off (rd_loop is the case rpv = v + d) *)
Definition pl_mid (cx : rdcx) (d : nat) (rpv : Z) ly3 S3 (W3 : world tfibsegs) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model) : Prop :=
  rd_com B cx EV_names [] ly3 S3 W3 regs3 mem3 md3 /\
  getr regs3 8 = w64 RD_M1 /\ getr regs3 9 = w64 (Z.of_nat d) /\ getr regs3 18 = w64 32 /\ getr regs3 19 = w64 5 /\
  getr regs3 20 = w64 RD_MASK1 /\ getr regs3 23 = w64 58 /\
  rd_slots_ok cx W3 mem3 (rd_loc_list cx) /\
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
  pl_keeps PL_LOOP regs3 regsB ->
  getr regsB 9 = w64 (Z.of_nat d') -> (d' <= 16)%nat ->
  val_mem tfibsegs (mrestrict (w_H W3) memB) (cx_sp cx) 8 rpv' ->
  pl_mid cx d' rpv' ly3 S3 W3 regsB memB mdB.
Proof.
intros cx d d' rpv rpv' ly3 S3 W3 regs3 mem3 md3 regsB memB mdB lo HMID HJ Hlo HloF HFlo HFhi HAV HP R9 Hd' Hrp.
pose proof HMID as (HCOM & R8 & _ & R18 & R19 & R20 & R23 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof asan_consts as (CC & _).
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (KL : g3_low_kept W3 W3 mem3 memB).
{ intros a Ha. apply HAV; [lia|]. unfold pl_win. lia. }
split.
{ apply (pl_com_kept cx EV_names ly3 S3 W3 regs3 mem3 md3 regsB memB mdB lo HCOM HJ Hlo HloF HFlo HFhi HAV).
  apply (pl_keeps_sub PL_COM PL_LOOP); [pl_sub | exact HP]. }
split; [rewrite (HP 8%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R8|].
split; [exact R9|].
split; [rewrite (HP 18%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R18|].
split; [rewrite (HP 19%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R19|].
split; [rewrite (HP 20%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R20|].
split; [rewrite (HP 23%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R23|].
split.
{ apply (pl_slots_kept cx W3 W3 mem3 memB _ HSLOTS). intros s Hs i Hi.
  assert (Hoff : 16 <= fst s <= 96)
    by (cbv [rd_loc_list In] in Hs; repeat (destruct Hs as [<-|Hs]; [cbn; lia|]); destruct Hs).
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

(* rd_PL without a3 = n: what survives isalnum's clobber of the argument registers *)
Definition pl_core (cx : rdcx) (i d f s11 p1 p2 p3 o q : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  let tb := cx_tb cx in let ub := cx_ub cx in let n := (length ub - o)%nat in
  rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 /\ rd_acc cx i d f /\ (i < length tb)%nat /\
  rd_decl cx i s11 p1 p2 p3 /\
  find_idx (fun c => c =? 62) (skipn (S p3) tb) = Some o /\ (o < length ub)%nat /\
  firstn o (skipn (S p3) tb) = firstn o ub /\
  last (skipn o ub) 0 <> 46 /\ (q < n)%nat /\ forallb plain_ok (firstn q (skipn o ub)) = true /\
  rd_slots_ok cx W3 mem3 [(0x08, cx_u cx + Z.of_nat o); (0x30, cx_u cx + Z.of_nat o); (0x38, cx_u cx + Z.of_nat o);
                          (0x40, RD_M1 - (cx_u cx + Z.of_nat o)); (0x48, Z.of_nat p2 - Z.of_nat p1)] /\
  getr regs3 21 = w64 (cx_t cx + Z.of_nat (S p3) + Z.of_nat o) /\
  getr regs3 22 = w64 (cx_t cx + Z.of_nat p1) /\ getr regs3 24 = w64 (Z.of_nat q).

Lemma pl_core_of_PL : forall cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3,
  rd_PL B cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 ->
  pl_core cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 H.
unfold rd_PL in H. unfold pl_core. cbv zeta in H |- *.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & _ & H13 & H14 & H15).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
split; [exact H11|]. split; [exact H13|]. split; [exact H14 | exact H15].
Qed.

Lemma pl_PL_of_core : forall cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3,
  pl_core cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 ->
  getr regs3 13 = w64 (Z.of_nat (length (cx_ub cx) - o)) ->
  rd_PL B cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 H R13.
unfold rd_PL. unfold pl_core in H. cbv zeta in H |- *.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H13 & H14 & H15).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
split; [exact H11|]. split; [exact R13|]. split; [exact H13|]. split; [exact H14 | exact H15].
Qed.

Lemma pl_core_kept : forall cx i d f s11 p1 p2 p3 o q ly3 S3 (W3 : world tfibsegs) regs3 mem3 md3 regsB memB mdB lo,
  pl_core cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 memB mdB EV_names ->
  alloc_ceiling <= lo -> lo <= cx_F cx -> alloc_ceiling + 4096 <= cx_F cx -> cx_sp cx + 16 <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pl_win cx lo a -> aview tfibsegs (w_H W3) memB a = aview tfibsegs (w_H W3) mem3 a) ->
  pl_keeps PL_CORE regs3 regsB ->
  val_mem tfibsegs (mrestrict (w_H W3) memB) (cx_sp cx) 8 (cx_v cx + Z.of_nat d) ->
  pl_core cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regsB memB mdB.
Proof.
intros cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 regsB memB mdB lo HC HJ Hlo HloF HFlo HFhi HAV HP Hrp.
pose proof asan_consts as (CC & _).
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
unfold pl_core in HC |- *. cbv zeta in HC |- *.
destruct HC as (HLOOP & HACC & Hilt & HDECL & HFI & Ho & HFirst & HLast & Hqn & HPlainq & HSL & R21 & R22 & R24).
pose proof (pl_mid_of_loop cx d ly3 S3 W3 regs3 mem3 md3 HLOOP) as HMID.
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdle).
split.
{ apply pl_loop_of_mid.
  apply (pl_mid_kept cx d d (cx_v cx + Z.of_nat d) (cx_v cx + Z.of_nat d) ly3 S3 W3 regs3 mem3 md3 regsB memB mdB lo
    HMID HJ Hlo HloF HFlo HFhi HAV ltac:(apply (pl_keeps_sub PL_LOOP PL_CORE); [pl_sub | exact HP]));
    [rewrite (HP 9%bv ltac:(cbv [PL_CORE In]; tauto)); exact (proj1 (proj2 (proj2 HMID))) | exact Hdle | exact Hrp]. }
split; [exact HACC|]. split; [exact Hilt|]. split; [exact HDECL|]. split; [exact HFI|]. split; [exact Ho|].
split; [exact HFirst|]. split; [exact HLast|]. split; [exact Hqn|]. split; [exact HPlainq|].
split.
{ apply (pl_slots_kept cx W3 W3 mem3 memB _ HSL). intros ss Hss j Hj. cbn in Hj.
  assert (Hoff : 8 <= fst ss <= 72)
    by (cbv [In] in Hss; repeat (destruct Hss as [<-|Hss]; [cbn; lia|]); destruct Hss).
  apply HAV; [lia|]. unfold pl_win. lia. }
split; [rewrite (HP 21%bv ltac:(cbv [PL_CORE In]; tauto)); exact R21|].
split; [rewrite (HP 22%bv ltac:(cbv [PL_CORE In]; tauto)); exact R22
       |rewrite (HP 24%bv ltac:(cbv [PL_CORE In]; tauto)); exact R24].
Qed.

(* ---- the loop's state across the call to has_prefixed ---- *)
Lemma pl_mid_hp : forall cx d rpv ly3 S3 (W3 : world tfibsegs) regs3 mem3 md3 ly5 S5 W5 regs5 mem5 md5,
  fm_img_facts tfibsegs B ->
  pl_mid cx d rpv ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_has_prefixed (cx_F cx) [] ly3 S3 W3 mem3 md3 [] ly5 S5 W5 mem5 md5 0 ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly5 S5 W5 mem5 md5 EV_names ->
  ablocks B ly5 S5 = ablocks B ly3 S3 ->
  pl_keeps PL_LOOP regs3 regs5 ->
  fm_glob tfibsegs W5 mem5 (cx_live cx) (Z.max (cx_peak cx) (cx_live cx + cx_ulen cx + 3)) (cx_cnt cx + 1)
    (cx_fail cx) ->
  getr regs5 9 = w64 (Z.of_nat d) ->
  alloc_ceiling + 4096 <= cx_F cx -> cx_sp cx + 16 <= 2 ^ 47 ->
  pl_mid cx d rpv ly5 S5 W5 regs5 mem5 md5.
Proof.
intros cx d rpv ly3 S3 W3 regs3 mem3 md3 ly5 S5 W5 regs5 mem5 md5 HIMG HMID HJhp HJ Hablk HPS HGL5 R9 HFlo HFhi.
pose proof asan_consts as (CC & _).
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (FHP : STK_has_prefixed = 8320) by reflexivity.
pose proof HMID as (HCOM & R8 & _ & R18 & R19 & R20 & R23 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof HCOM as (HJ0 & Hk & R2 & R3 & R4 & R27 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HJhp as (_ & _ & _ & _ & _ & _ & _ & _ & HAVh & _).
assert (Hinc : forall x, In x (ablocks B ly3 S3) -> In x (ablocks B ly5 S5)) by (rewrite Hablk; tauto).
assert (HRO5 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W5) mem5))
  by exact (pl_arodata_kept STK_has_prefixed (cx_F cx) ly3 S3 W3 mem3 md3 [] ly5 S5 W5 mem5 md5 0 HJhp HRO).
assert (HCOM5 : rd_com B cx EV_names [] ly5 S5 W5 regs5 mem5 md5).
{ split; [change (unpoison [] mem5) with mem5; exact HJ|]. split; [exact Hk|].
  split; [rewrite (HPS 2%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R2|].
  split; [rewrite (HPS 3%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R3|].
  split; [rewrite (HPS 4%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R4|].
  split; [rewrite (HPS 27%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R27|].
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
split; [rewrite (HPS 8%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R8|].
split; [exact R9|].
split; [rewrite (HPS 18%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R18|].
split; [rewrite (HPS 19%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R19|].
split; [rewrite (HPS 20%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R20|].
split; [rewrite (HPS 23%bv ltac:(cbv [PL_LOOP In]; tauto)); exact R23|].
split.
{ apply (pl_slots_kept cx W3 W5 mem3 mem5 _ HSLOTS). intros ss Hss j Hj. cbn in Hj.
  assert (Hoff : 16 <= fst ss <= 96)
    by (cbv [rd_loc_list In] in Hss; repeat (destruct Hss as [<-|Hss]; [cbn; lia|]); destruct Hss).
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

Ltac pl_num H := rewrite H; unfold w64; try (rewrite unsigned_lit_small by lia); (f_equal; lia).

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

(* 0x82338, after has_prefixed: *readings already carries the extra reading; s1 = d, s8 = d + 1, s9 = 1 *)
Definition pl_atC (cx : rdcx) (i d f s11 p1 p2 p3 o : nat) ly4 S4 (W4 : world tfibsegs) regs4 mem4 md4 : Prop :=
  pl_mid cx d (cx_v cx + Z.of_nat d + 1) ly4 S4 W4 regs4 mem4 md4 /\
  rd_acc cx i d f /\ (i < length (cx_tb cx))%nat /\ rd_decl cx i s11 p1 p2 p3 /\
  find_idx (fun c => c =? 62) (skipn (S p3) (cx_tb cx)) = Some o /\ (o < length (cx_ub cx))%nat /\
  firstn o (skipn (S p3) (cx_tb cx)) = firstn o (cx_ub cx) /\
  last (skipn o (cx_ub cx)) 0 <> 46 /\ forallb plain_ok (skipn o (cx_ub cx)) = true /\ (d < 16)%nat /\
  getr regs4 21 = w64 (cx_t cx + Z.of_nat (S p3) + Z.of_nat o) /\
  getr regs4 24 = w64 (Z.of_nat d + 1) /\ getr regs4 25 = w64 1.

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
destruct HC as (HMID & HACC & Hilt & HDECL & HFI & Ho & HFirst & HLast & HPlain & Hd16 & R21 & R24 & R25).
pose proof HMID as (HCOM & R8 & R9 & R18 & R19 & R20 & R23 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof HCOM as (HJ & Hk & R2 & R3 & R4 & R27 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HB as (HAN & HCTX & HROb & H10b & H11b & H12b & Hpresb & Htopr & Hvb & Hv63 & Ctb & Cub & Ktb & Kub &
  Hub255 & Htbmax & HGb & Hlv & Hcntb & Hevb & Hlbb & Hrab & Hchb).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSP : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (FFR : STK_readings = 16624) by reflexivity.
assert (HFlo : alloc_ceiling + 4096 <= cx_F cx) by lia.
assert (HFhi : cx_sp cx + 16 <= 2 ^ 47) by lia.
assert (HF16 : cx_F cx mod 16 = 0)
  by (rewrite HFsp; replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia; rewrite Z_mod_plus_full;
      rewrite HSP; exact Hal16).
pose proof Ct as ((_ & _) & Ht1 & Ht2 & _).
assert (Hclose : (S p3 + o < length (cx_tb cx))%nat)
  by (pose proof (pl_find_idx_lt _ _ _ HFI) as Hlt; rewrite length_skipn in Hlt; lia).
pose proof (plC_entry W4 regs4 mem4 (cx_F cx) (cx_t cx + Z.of_nat (S p3) + Z.of_nat o) (Z.of_nat d + 1)
  R2 R27 R8 R21 R24 ltac:(lia) HF16 ltac:(lia) ltac:(lia)) as HS.
set (E := Ereg regs4 ([] : list word)) in *.
assert (E2 : ew E 2 = w64 (cx_F cx)) by (unfold E; rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl); exact R2).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite E2; apply unsigned_lit_small; lia).
assert (E10 : ew E 10 = w64 res) by (unfold E; rewrite (ew_Ereg_nat regs4 _ 10 10%bv eq_refl); exact R10).
assert (E21 : ew E 21 = w64 (cx_t cx + Z.of_nat (S p3) + Z.of_nat o))
  by (unfold E; rewrite (ew_Ereg_nat regs4 _ 21 21%bv eq_refl); exact R21).
assert (E24 : ew E 24 = w64 (Z.of_nat d + 1))
  by (unfold E; rewrite (ew_Ereg_nat regs4 _ 24 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = w64 1) by (unfold E; rewrite (ew_Ereg_nat regs4 _ 25 25%bv eq_refl); exact R25).
assert (SHOK : sh_ok tfibsegs PL_Bx [] E
  (mrestrict (w_H W4) (ms_mem (mkst regs4 (Z_to_bv 64 PL_C) mem4 (seg_rom tfibsegs))))) by constructor.
assert (Hne : skipn o (cx_ub cx) <> [])
  by (intros Hnil; apply (f_equal (@length Z)) in Hnil; rewrite length_skipn in Hnil; cbn in Hnil; lia).
assert (Hmatch : matches (cx_tb cx) (cx_ub cx) (S p3) o = true).
{ rewrite (pl_matches _ _ _ _ Ho HFirst), (pl_plain_name _ Hne HLast). exact HPlain. }
pose proof HDECL as HDECL2. unfold rd_decl in HDECL2. cbv zeta in HDECL2.
destruct HDECL2 as (Hhead & Hs11 & Hsp & Hp1 & Hp2 & Hc58 & Hp3 & Hc60 & Hlen3).
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
  assert (KE0 : forall a, 0 <= a < 2 ^ 64 ->
    aview tfibsegs (w_H W4) (ms_mem ms) a = aview tfibsegs (w_H W4) mem4 a).
  { intros a Ha. apply (g3_aview_frame E (ss_mem ss_C) (w_H W4) mem4 (ms_mem ms) HFr a Ha).
    intros (rr & Hin & Hr). cbn [ss_C ss_mem In] in Hin. destruct Hin. }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ pl_win cx (cx_F cx) a ->
    aview tfibsegs (w_H W4) (ms_mem ms) a = aview tfibsegs (w_H W4) mem4 a)
    by (intros a Ha _; apply KE0; lia).
  assert (KL : g3_low_kept W4 W4 mem4 (ms_mem ms)) by (intros a Ha; apply KE0; lia).
  pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs4 ([] : list word) PL_COM HS
    ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  eapply (rd_ret_holds B CTX cx EV_names ly4 S4 W4 (ms_regs ms) (ms_mem ms) _ 1 HB).
  - exact (pl_com_kept cx EV_names ly4 S4 W4 regs4 mem4 _ (ms_regs ms) (ms_mem ms) _ (cx_F cx)
      HCOM HJ ltac:(lia) ltac:(lia) HFlo HFhi KE KR).
  - rreg HS (25%bv : bv 5) Q25. rewrite Q25. exact E25.
  - lia.
  - split; [exact HPERM|]. split.
    + right. right. split; [exact Hub|]. split; [exact Hcf|]. split.
      * destruct HACC as (_ & _ & Hnames & _). symmetry. rewrite Hnames. exact Hscan.
      * exact (g3_fm_glob_kept W4 W4 mem4 (ms_mem ms) _ _ _ _ HGL KL).
    + rewrite Hub0, Hcf0. cbn [orb].
      destruct HACC as (_ & _ & _ & Hnr). rewrite Hnr, Hread.
      apply (g3_val_mem_kept W4 W4 mem4 (ms_mem ms));
        [replace (cx_v cx + Z.of_nat (d + 1)) with (cx_v cx + Z.of_nat d + 1) by lia; exact HRP|].
      intros j Hj. cbn in Hj. apply KE0; lia. }
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
  assert (KE0 : forall a, 0 <= a < 2 ^ 64 ->
    aview tfibsegs (w_H W4) (ms_mem ms) a = aview tfibsegs (w_H W4) mem4 a).
  { intros a Ha. apply (g3_aview_frame E (ss_mem ss_C) (w_H W4) mem4 (ms_mem ms) HFr a Ha).
    intros (rr & Hin & Hr). cbn [ss_C ss_mem In] in Hin. destruct Hin. }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ pl_win cx (cx_F cx) a ->
    aview tfibsegs (w_H W4) (ms_mem ms) a = aview tfibsegs (w_H W4) mem4 a)
    by (intros a Ha _; apply KE0; lia).
  pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs4 ([] : list word) PL_LOOP HS
    ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  rreg HS (9%bv : bv 5) Q9. rreg HS (21%bv : bv 5) Q21.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  eapply (HSEGL cx (S (S p3 + o)) (S d) ly4 S4 W4 (ms_regs ms) (ms_mem ms) _ HB).
  split; [|split].
  - apply pl_loop_of_mid.
    apply (pl_mid_kept cx d (S d) (cx_v cx + Z.of_nat d + 1) (cx_v cx + Z.of_nat (S d))
      ly4 S4 W4 regs4 mem4 _ (ms_regs ms) (ms_mem ms) _ (cx_F cx) HMID HJ ltac:(lia) ltac:(lia) HFlo HFhi
      KE KR).
    + rewrite Q9. cbn [sv_denot ew ewset Nat.eqb]. pl_num E24.
    + lia.
    + apply (g3_val_mem_kept W4 W4 mem4 (ms_mem ms));
        [replace (cx_v cx + Z.of_nat (S d)) with (cx_v cx + Z.of_nat d + 1) by lia; exact HRP|].
      intros j Hj. cbn in Hj. apply KE0; lia.
  - destruct HACC as (Hi1 & Hi2 & Hi3 & Hi4).
    split; [lia|]. split; [lia|]. split; [rewrite Hi3; exact Hscan|]. rewrite Hi4, Hread. lia.
  - rewrite Q21. cbn [sv_denot ew ewset Nat.eqb].
    pl_num E21. }
Qed.

Lemma pl_from_N : forall f cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3,
  rd_seg_L B CTX f -> rd_base B CTX cx ->
  pl_core cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 ->
  plain_ok (byte_at (cx_ub cx) (o + q)) = false ->
  SRr tfibsegs W3 (cfg_at tfibsegs PL_N regs3 mem3 md3) (rd_post B cx).
Proof.
intros f cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 HSEGL HB HPL Hnp.
pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs. pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (CC & _).
unfold pl_core in HPL. cbv zeta in HPL.
destruct HPL as (HLOOP & HACC & Hilt & HDECL & HFI & Ho & HFirst & HLast & Hqn & HPlainq & HSL & R21 & R22 & R24).
pose proof (pl_mid_of_loop cx d ly3 S3 W3 regs3 mem3 md3 HLOOP) as HMID.
pose proof HMID as (HCOM & R8 & R9 & R18 & R19 & R20 & R23 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof HCOM as (HJ & Hk & R2 & R3 & R4 & R27 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HB as (HAN & HCTX & HROb & H10b & H11b & H12b & Hpresb & Htopr & Hvb & Hv63 & Ctb & Cub & Ktb & Kub &
  Hub255 & Htbmax & HGb & Hlv & Hcntb & Hevb & Hlbb & Hrab & Hchb).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSP : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (FFR : STK_readings = 16624) by reflexivity.
assert (HFlo : alloc_ceiling + 4096 <= cx_F cx) by lia.
assert (HFhi : cx_sp cx + 16 <= 2 ^ 47) by lia.
assert (HF16 : cx_F cx mod 16 = 0)
  by (rewrite HFsp; replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia; rewrite Z_mod_plus_full;
      rewrite HSP; exact Hal16).
pose proof Ct as ((_ & _) & Ht1 & Ht2 & _).
assert (Hclose : (S p3 + o < length (cx_tb cx))%nat)
  by (pose proof (pl_find_idx_lt _ _ _ HFI) as Hlt; rewrite length_skipn in Hlt; lia).
pose proof (plN_entry W3 regs3 mem3 (cx_F cx) (cx_t cx + Z.of_nat (S p3) + Z.of_nat o)
  R2 R27 R8 R21 ltac:(lia) HF16 ltac:(lia)) as HS.
set (E := Ereg regs3 ([] : list word)) in *.
assert (E2 : ew E 2 = w64 (cx_F cx)) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); exact R2).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite E2; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = w64 (Z.of_nat d)) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = w64 (cx_t cx + Z.of_nat (S p3) + Z.of_nat o))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 21 21%bv eq_refl); exact R21).
assert (SHOK : sh_ok tfibsegs PL_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 PL_N) mem3 (seg_rom tfibsegs))))) by constructor.
assert (Hne : skipn o (cx_ub cx) <> [])
  by (intros Hnil; apply (f_equal (@length Z)) in Hnil; rewrite length_skipn in Hnil; cbn in Hnil; lia).
assert (Hfa : forallb plain_ok (skipn o (cx_ub cx)) = false).
{ apply (pl_forallb_false plain_ok _ q); [rewrite length_skipn; lia|]. rewrite pl_nth_skipn. exact Hnp. }
assert (Hmatch : matches (cx_tb cx) (cx_ub cx) (S p3) o = false).
{ rewrite (pl_matches _ _ _ _ Ho HFirst), (pl_plain_name _ Hne HLast). exact Hfa. }
pose proof HDECL as HDECL2. unfold rd_decl in HDECL2. cbv zeta in HDECL2.
destruct HDECL2 as (Hhead & Hs11 & Hsp & Hp1 & Hp2 & Hc58 & Hp3 & Hc60 & Hlen3).
assert (Hdecl : decl (cx_tb cx) i = DFound p1 (p2 - p1) (S p3) o (S p3 + o))
  by exact (pl_decl_found (cx_tb cx) i s11 p1 p2 p3 o Hhead Hsp Hp1 Hp2 Hc58 Hp3 Hc60 HFI).
destruct (pl_sc_nomatch (cx_tb cx) (cx_ub cx) i d f p1 (p2 - p1) (S p3) o (S p3 + o) Hilt Hdecl Hmatch)
  as [Hscan Hread].
change (unpoison [] mem3) with mem3 in HJ.
unfold cfg_at. change (w64 PL_N) with (Z_to_bv 64 PL_N).
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 PL_N) mem3 (seg_rom tfibsegs))) in HJ.
aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan RD_L; [pl_awr U2|].
assert (KE0 : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha. apply (g3_aview_frame E (ss_mem ss_N) (w_H W3) mem3 (ms_mem ms) HFr a Ha).
  intros (rr & Hin & Hr). cbn [ss_N ss_mem In] in Hin. destruct Hin. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ pl_win cx (cx_F cx) a ->
  aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a) by (intros a Ha _; apply KE0; lia).
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 ([] : list word) PL_LOOP HS
  ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
rreg HS (9%bv : bv 5) Q9. rreg HS (21%bv : bv 5) Q21.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply (HSEGL cx (S (S p3 + o)) d ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ HB).
split; [|split].
- apply pl_loop_of_mid.
  apply (pl_mid_kept cx d d (cx_v cx + Z.of_nat d) (cx_v cx + Z.of_nat d)
    ly3 S3 W3 regs3 mem3 _ (ms_regs ms) (ms_mem ms) _ (cx_F cx) HMID HJ ltac:(lia) ltac:(lia) HFlo HFhi KE KR).
  + rewrite Q9. cbn [sv_denot ew ewset Nat.eqb]. pl_num E9.
  + lia.
  + apply (g3_val_mem_kept W3 W3 mem3 (ms_mem ms)); [exact HRP|]. intros j Hj. cbn in Hj. apply KE0; lia.
- destruct HACC as (Hi1 & Hi2 & Hi3 & Hi4).
  split; [lia|]. split; [lia|]. split; [rewrite Hi3; exact Hscan|]. rewrite Hi4, Hread. lia.
- rewrite Q21. cbn [sv_denot ew ewset Nat.eqb].
  pl_num E21.
Qed.

(* the read_again test at 0x82300: blt 16, s8 with s8 = d + 1 *)
Lemma pl_D_d : forall dv, 0 <= dv <= 16 -> pl_D 9 BC_LT (SLit 16) (SOff 9 1) dv = (16 <? dv + 1).
Proof.
  intros dv Hd.
  assert (H : forallb (fun z => Bool.eqb (pl_D 9 BC_LT (SLit 16) (SOff 9 1) z) (16 <? z + 1))
    (map Z.of_nat (seq 0 17)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  specialize (H dv ltac:(apply in_map_iff; exists (Z.to_nat dv); split; [apply Z2Nat.id; lia | apply in_seq; lia])).
  cbn beta in H. destruct (pl_D 9 BC_LT (SLit 16) (SOff 9 1) dv), (16 <? dv + 1); cbn in H; congruence.
Qed.

Lemma pl_from_P : forall f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3,
  rd_seg_L B CTX f -> rd_seg_PL B CTX (S f) m -> (length (cx_ub cx) - o - q <= S m)%nat ->
  rd_base B CTX cx ->
  pl_core cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 ->
  getr regs3 13 = w64 (Z.of_nat (length (cx_ub cx) - o)) ->
  plain_ok (byte_at (cx_ub cx) (o + q)) = true ->
  SRr tfibsegs W3 (cfg_at tfibsegs PL_P regs3 mem3 md3) (rd_post B cx).
Proof.
intros f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 HSEGL HSEGPL Hm HB HPL R13 Hpl.
pose proof HPL as HPL0.
pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs. pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (CC & _).
unfold pl_core in HPL. cbv zeta in HPL.
destruct HPL as (HLOOP & HACC & Hilt & HDECL & HFI & Ho & HFirst & HLast & Hqn & HPlainq & HSL & R21 & R22 & R24).
pose proof (pl_mid_of_loop cx d ly3 S3 W3 regs3 mem3 md3 HLOOP) as HMID.
pose proof HMID as (HCOM & R8 & R9 & R18 & R19 & R20 & R23 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof HCOM as (HJ & Hk & R2 & R3 & R4 & R27 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HB as (HAN & HCTX & HROb & H10b & H11b & H12b & Hpresb & Htopr & Hvb & Hv63 & Ctb & Cub & Ktb & Kub &
  Hub255 & Htbmax & HGb & Hlv & Hcntb & Hevb & Hlbb & Hrab & Hchb).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARj & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HSP : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (FFR : STK_readings = 16624) by reflexivity.
assert (FHP : STK_has_prefixed = 8320) by reflexivity.
assert (HFlo : alloc_ceiling + 4096 <= cx_F cx) by lia.
assert (HFhi : cx_sp cx + 16 <= 2 ^ 47) by lia.
assert (HF16 : cx_F cx mod 16 = 0)
  by (rewrite HFsp; replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia; rewrite Z_mod_plus_full;
      rewrite HSP; exact Hal16).
assert (Hsp8 : cx_sp cx mod 8 = 0).
{ pose proof (Z.div_mod (cx_sp cx) 16 ltac:(lia)) as D.
  assert (Hmm : cx_sp cx mod 16 = 0) by (rewrite HSP; exact Hal16).
  rewrite Hmm, Z.add_0_r in D. rewrite D.
  replace (16 * (cx_sp cx / 16)) with (2 * (cx_sp cx / 16) * 8) by lia. apply Z_mod_mult. }
pose proof Ct as ((_ & _) & Ht1 & Ht2 & _).
pose proof Cu as ((HGu & HNZu) & Hu1 & Hu2 & _).
assert (Hclose : (S p3 + o < length (cx_tb cx))%nat)
  by (pose proof (pl_find_idx_lt _ _ _ HFI) as Hlt; rewrite length_skipn in Hlt; lia).
assert (Hoq : (o + q < length (cx_ub cx))%nat) by lia.
(* the frame slots this segment reads *)
pose proof HSLOTS as HSL2. unfold rd_slots_ok in HSL2. cbv [rd_loc_list] in HSL2.
apply Forall_cons_iff in HSL2 as [SL10 HSL2]. apply Forall_cons_iff in HSL2 as [SL18 HSL2].
apply Forall_cons_iff in HSL2 as [SL20 HSL2]. apply Forall_cons_iff in HSL2 as [SL28 HSL2].
apply Forall_cons_iff in HSL2 as [SL50 HSL2]. cbn [fst snd] in SL10, SL18, SL20, SL28, SL50.
pose proof HSL as HSL3. unfold rd_slots_ok in HSL3.
apply Forall_cons_iff in HSL3 as [SL08 HSL3]. apply Forall_cons_iff in HSL3 as [SL30 HSL3].
apply Forall_cons_iff in HSL3 as [SL38 HSL3]. apply Forall_cons_iff in HSL3 as [SL40 HSL3].
apply Forall_cons_iff in HSL3 as [SL48 _]. cbn [fst snd] in SL08, SL30, SL38, SL40, SL48.
pose proof (plP_entry W3 regs3 mem3 (cx_F cx) (Z.of_nat d) (Z.of_nat (length (cx_ub cx) - o)) (Z.of_nat q)
  (cx_u cx + Z.of_nat o) (cx_t cx) (Z.of_nat p2 - Z.of_nat p1) (cx_v cx + Z.of_nat d)
  R2 R27 R9 R13 R24 ltac:(lia) HF16 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) (proj2 SL48) ltac:(lia)
  (proj1 SL08) ltac:(replace (cx_F cx + 208) with (cx_sp cx) by lia; exact (proj1 SL10))
  (proj1 SL48) (proj1 SL50)
  ltac:(replace (cx_F cx + 208) with (cx_sp cx) by lia; exact HRP)
  ltac:(intros a Ha; apply (apresent_writable tfibsegs); apply Hpresj; lia)) as HS.
set (E := Ereg regs3 [w64 (cx_u cx + Z.of_nat o); w64 (cx_t cx); w64 (Z.of_nat p2 - Z.of_nat p1);
  w64 (cx_v cx + Z.of_nat d)]) in *.
assert (E2 : ew E 2 = w64 (cx_F cx)) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); exact R2).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite E2; apply unsigned_lit_small; lia).
assert (E3a : ew E 3 = getr regs3 3) by (unfold E; exact (ew_Ereg_nat regs3 _ 3 3%bv eq_refl)).
assert (E4a : ew E 4 = getr regs3 4) by (unfold E; exact (ew_Ereg_nat regs3 _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = w64 RD_M1) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 (Z.of_nat d)) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl); exact R9).
assert (E13 : ew E 13 = w64 (Z.of_nat (length (cx_ub cx) - o)))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 13 13%bv eq_refl); exact R13).
assert (E21 : ew E 21 = w64 (cx_t cx + Z.of_nat (S p3) + Z.of_nat o))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 21 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 (cx_t cx + Z.of_nat p1))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 22 22%bv eq_refl); exact R22).
assert (E24 : ew E 24 = w64 (Z.of_nat q)) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 24 24%bv eq_refl); exact R24).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = w64 (cx_u cx + Z.of_nat o)) by (unfold E; exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = w64 (cx_t cx)) by (unfold E; exact (ew_Ereg_extra regs3 _ 1)).
assert (E34 : ew E 34 = w64 (Z.of_nat p2 - Z.of_nat p1)) by (unfold E; exact (ew_Ereg_extra regs3 _ 2)).
assert (E35 : ew E 35 = w64 (cx_v cx + Z.of_nat d)) by (unfold E; exact (ew_Ereg_extra regs3 _ 3)).
assert (SHOK : sh_ok tfibsegs PL_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 PL_P) mem3 (seg_rom tfibsegs))))) by constructor.
assert (Hne : skipn o (cx_ub cx) <> [])
  by (intros Hnil; apply (f_equal (@length Z)) in Hnil; rewrite length_skipn in Hnil; cbn in Hnil; lia).
pose proof HDECL as HDECL2. unfold rd_decl in HDECL2. cbv zeta in HDECL2.
destruct HDECL2 as (Hhead & Hs11 & Hsp & Hp1 & Hp2 & Hc58 & Hp3 & Hc60 & Hlen3).
assert (Hdecl : decl (cx_tb cx) i = DFound p1 (p2 - p1) (S p3) o (S p3 + o))
  by exact (pl_decl_found (cx_tb cx) i s11 p1 p2 p3 o Hhead Hsp Hp1 Hp2 Hc58 Hp3 Hc60 HFI).
assert (Hub0 : (length (cx_ub cx) =? 0)%nat = false) by (destruct (cx_ub cx); [congruence | reflexivity]).
assert (Hcf0 : (cx_cnt cx =? cx_fail cx) = false) by (apply Z.eqb_neq; exact Hcf).
change (unpoison [] mem3) with mem3 in HJ.
unfold cfg_at. change (w64 PL_P) with (Z_to_bv 64 PL_P).
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 PL_P) mem3 (seg_rom tfibsegs))) in HJ.
aj_run_tok rd_tbl_ok HS HJ SHOK PL_Bspan; [pl_awr U2|].
assert (KE1 : pl_same cx W3 mem3 (ms_mem ms)).
{ intros a Ha Hn. apply (g3_aview_frame E (ss_mem ss_P) (w_H W3) mem3 (ms_mem ms) HFr a Ha).
  intros (rr & Hin & Hr). cbn [ss_P ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[]]];
    cbn [pl_fr_P pl_fr_rp YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite U2 in Hr; apply Hn; unfold pl_win; lia. }
srr_branch_tok rd_tbl_ok HS SHOK PL_Bspan.
{ (* bytes left: the back edge at 0x8227c with q + 1 *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom E 13 (Z.of_nat (length (cx_ub cx) - o)) E13 ltac:(lia)) in Hc.
  rewrite (U_atom_off E 24 (Z.of_nat q) 1 E24 ltac:(lia) ltac:(lia)) in Hc.
  apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  assert (HqS : (S q < length (cx_ub cx) - o)%nat) by lia.
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan PL_A; [pl_awr U2|].
  lazymatch type of HFr0 with frame_of ?Ex ?rs _ _ =>
    assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
    assert (KE2 : pl_same cx W3 (ms_mem ms) (ms_mem ms0)) by
      (intros a Ha Hn; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms) (ms_mem ms0) HFr0 a Ha);
       intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
       destruct Hin as [<-|[<-|[]]];
         cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr;
         apply Hn; unfold pl_win; lia);
    clear X2 end.
  assert (KE : pl_same cx W3 mem3 (ms_mem ms0)) by exact (pl_same_trans cx W3 _ _ _ KE1 KE2).
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRrp;
    cbn [ms_mem restrict] in HRrp end.
  assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms0)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
  { replace (cx_sp cx) with (cx_F cx + 208) by lia.
    apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 208 8%N (SOff 35 0) (cx_v cx + Z.of_nat d) HRrp
      ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, unsigned_lit_small by lia; unfold w64; f_equal; lia)
      ltac:(cbn; lia) ltac:(cbn; lia)). }
  pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_KEEP1 HS
    ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  rreg HS (24%bv : bv 5) Q24.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  eapply (HSEGPL cx i d s11 p1 p2 p3 o (S q) ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) _ ltac:(lia) HB).
  apply pl_PL_of_core; [|rewrite (KR 13%bv ltac:(cbv [PL_KEEP1 In]; tauto)); exact R13].
  unfold pl_core. cbv zeta.
  split.
  { apply pl_loop_of_mid.
    apply (pl_mid_kept cx d d (cx_v cx + Z.of_nat d) (cx_v cx + Z.of_nat d) ly3 S3 W3 regs3 mem3 _
      (ms_regs ms0) (ms_mem ms0) _ (cx_F cx) HMID HJ ltac:(lia) ltac:(lia) HFlo HFhi KE
      ltac:(apply (pl_keeps_sub PL_LOOP PL_KEEP1); [pl_sub | exact KR]));
      [rewrite (KR 9%bv ltac:(cbv [PL_KEEP1 In]; tauto)); exact R9 | lia | exact Vrp]. }
  split; [exact HACC|]. split; [exact Hilt|]. split; [exact HDECL|]. split; [exact HFI|]. split; [exact Ho|].
  split; [exact HFirst|]. split; [exact HLast|]. split; [exact HqS|].
  split.
  { apply (pl_forallb_S plain_ok _ q); [rewrite length_skipn; lia | exact HPlainq|].
    rewrite pl_nth_skipn. exact Hpl. }
  split.
  { apply (pl_slots_kept cx W3 W3 mem3 (ms_mem ms0) _ HSL). intros ss Hss j Hj. cbn in Hj.
    assert (Hoff : 8 <= fst ss <= 72)
      by (cbv [In] in Hss; repeat (destruct Hss as [<-|Hss]; [cbn; lia|]); destruct Hss).
    apply KE; [lia | unfold pl_win; lia]. }
  split; [rewrite (KR 21%bv ltac:(cbv [PL_KEEP1 In]; tauto)); exact R21|].
  split; [rewrite (KR 22%bv ltac:(cbv [PL_KEEP1 In]; tauto)); exact R22|].
  rewrite Q24. cbn [sv_denot ew ewset Nat.eqb]. pl_num E24. }
{ (* the last byte: the declaration matches the uri *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom E 13 (Z.of_nat (length (cx_ub cx) - o)) E13 ltac:(lia)) in Hc.
  rewrite (U_atom_off E 24 (Z.of_nat q) 1 E24 ltac:(lia) ltac:(lia)) in Hc.
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
       destruct Hin as [<-|[<-|[]]];
         cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr;
         apply Hn; unfold pl_win; lia);
    clear X2 end.
  assert (KE12 : pl_same cx W3 mem3 (ms_mem ms0)) by exact (pl_same_trans cx W3 _ _ _ KE1 KE2).
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (H9' : ew Ex 9 = Z_to_bv 64 (Z.of_nat d)) by (cbn [ew ewset Nat.eqb]; exact E9) end.
  srr_branch_tok rd_tbl_ok HS SHOK PL_Bspan.
  { (* read_again is already at its bound: the answer is 1 *)
    erewrite (pl_D_of 9 _ (Z.of_nat d) _ _ _ H9') in Hc0 by reflexivity.
    rewrite (pl_D_d (Z.of_nat d) ltac:(lia)) in Hc0. apply Z.ltb_lt in Hc0.
    destruct (pl_sc_cnt (cx_tb cx) (cx_ub cx) i d f p1 (p2 - p1) (S p3) o (S p3 + o) Hilt Hdecl Hmatch
      ltac:(lia)) as [Hscan Hread].
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan RD_R; [pl_awr U2|].
    lazymatch type of HFr1 with frame_of ?Ex ?rs _ _ =>
      assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
      assert (KE3 : pl_same cx W3 (ms_mem ms0) (ms_mem ms1)) by
        (intros a Ha Hn; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha);
         intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
         destruct Hin as [<-|[<-|[]]];
           cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr;
           apply Hn; unfold pl_win; lia);
      clear X2 end.
    assert (KE : pl_same cx W3 mem3 (ms_mem ms1)) by exact (pl_same_trans cx W3 _ _ _ KE12 KE3).
    assert (KL : g3_low_kept W3 W3 mem3 (ms_mem ms1))
      by (intros a Ha; apply KE; [lia | unfold pl_win; lia]).
    lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
      let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
      pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRrp;
      cbn [ms_mem restrict] in HRrp end.
    assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms1)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
    { replace (cx_sp cx) with (cx_F cx + 208) by lia.
      apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 208 8%N (SOff 35 0) (cx_v cx + Z.of_nat d) HRrp
        ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, unsigned_lit_small by lia; unfold w64; f_equal; lia)
        ltac:(cbn; lia) ltac:(cbn; lia)). }
    pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_COM HS
      ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    rreg HS (25%bv : bv 5) Q25.
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
    eapply (rd_ret_holds B CTX cx EV_names ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ 1 HB).
    - exact (pl_com_kept cx EV_names ly3 S3 W3 regs3 mem3 _ (ms_regs ms1) (ms_mem ms1) _ (cx_F cx)
        HCOM HJ ltac:(lia) ltac:(lia) HFlo HFhi KE KR).
    - rewrite Q25. reflexivity.
    - lia.
    - split; [exact HPERM|]. split.
      + right. right. split; [exact Hub|]. split; [exact Hcf|]. split.
        * destruct HACC as (_ & _ & Hnames & _). symmetry. rewrite Hnames. exact Hscan.
        * exact (g3_fm_glob_kept W3 W3 mem3 (ms_mem ms1) _ _ _ _ HGL KL).
      + rewrite Hub0, Hcf0. cbn [orb]. destruct HACC as (_ & _ & _ & Hnr). rewrite Hnr, Hread.
        rewrite Nat.add_0_r. exact Vrp. }
  { (* one more reading: ++*readings, then has_prefixed *)
    erewrite (pl_D_of 9 _ (Z.of_nat d) _ _ _ H9') in Hc0 by reflexivity.
    rewrite (pl_D_d (Z.of_nat d) ltac:(lia)) in Hc0. apply Z.ltb_ge in Hc0.
    assert (Hd16 : (d < 16)%nat) by lia.
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan A_has_prefixed; [ | pl_awr U2 | ].
    { (* the 8-byte check of *readings from the stack's zero shadow *)
      lazymatch goal with |- range_addressable (rd_of _ (mrestrict _ ?MM)) (U ?Ex _) _ _ =>
        assert (Y2 : U Ex (SOff 2 208) = cx_F cx + 208) by
          (apply (U_atom_off Ex 2 (cx_F cx) 208); [cbn [ew ewset Nat.eqb]; exact E2 | lia | lia]);
        apply (obl_of_range tfibsegs (w_H W3) MM Ex PL_Bx (U Ex (SOff 2 208)) 8 (cx_sp cx) 8);
        [ | unfold PL_Bx; apply (U_atom Ex 27 SHADOW_OFF);
            [cbn [ew ewset Nat.eqb]; exact E27 | unfold SHADOW_OFF; lia]
          | rewrite Y2; lia | rewrite Y2; lia ];
        apply (zero_shadow_range (aview tfibsegs (w_H W3) MM) SHADOW_OFF (cx_sp cx) 8);
        [ exact Hsp8 | reflexivity | ];
        intros j Hj; assert (Hj0 : j = 0) by (cbn in Hj; lia); subst j; rewrite Z.add_0_r;
        change (shadow_of_addr SHADOW_OFF (cx_sp cx)) with (shadow_addr (cx_sp cx));
        apply (g3_stk_sh0_of_AR B ly3 S3 W3 MM _ (cx_sp cx) (cx_sp cx + 1) (proj1 HJ)
          ltac:(rewrite Eslo; lia) ltac:(rewrite Eshi; lia)); lia end. }
    lazymatch type of HFr1 with frame_of ?Ex ?rs _ _ =>
      assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
      assert (KE3 : pl_same cx W3 (ms_mem ms0) (ms_mem ms1)) by
        (intros a Ha Hn; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha);
         intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
         destruct Hin as [<-|[<-|[]]];
           cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr;
           apply Hn; unfold pl_win; lia);
      clear X2 end.
    assert (KE : pl_same cx W3 mem3 (ms_mem ms1)) by exact (pl_same_trans cx W3 _ _ _ KE12 KE3).
    lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
      let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
      pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRrp;
      cbn [ms_mem restrict] in HRrp end.
    assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms1)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d + 1)).
    { replace (cx_sp cx) with (cx_F cx + 208) by lia.
      apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 208 8%N (SOff 35 1) (cx_v cx + Z.of_nat d + 1) HRrp
        ltac:(cbn [ew ewset Nat.eqb]; rewrite ?U2; reflexivity) ltac:(cbn; tauto)
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, unsigned_lit_small by lia; unfold w64; f_equal; lia)
        ltac:(cbn; lia) ltac:(cbn; lia)). }
    pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_KEEP2 HS
      ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    eassert (HMIDc : pl_mid cx d (cx_v cx + Z.of_nat d + 1) ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _).
    { apply (pl_mid_kept cx d d (cx_v cx + Z.of_nat d) (cx_v cx + Z.of_nat d + 1) ly3 S3 W3 regs3 mem3 _
        (ms_regs ms1) (ms_mem ms1) _ (cx_F cx) HMID HJ ltac:(lia) ltac:(lia) HFlo HFhi KE
        ltac:(apply (pl_keeps_sub PL_LOOP PL_KEEP2); [pl_sub | exact KR]));
        [rewrite (KR 9%bv ltac:(cbv [PL_KEEP2 In]; tauto)); exact R9 | lia | exact Vrp]. }
    pose proof HMIDc as (HCOMc & _ & R9c & _ & _ & _ & _ & _ & _ & _ & HGLc & _).
    pose proof HCOMc as (HJc & _ & Rc2 & Rc3 & Rc4 & Rc27 & _ & _ & HROc & Ctc & Cuc & Ktc & Kuc).
    rreg HS (1%bv : bv 5) Qra. rreg HS (2%bv : bv 5) Qsp. rreg HS (8%bv : bv 5) Qs0.
    rreg HS (10%bv : bv 5) Qa0. rreg HS (11%bv : bv 5) Qa1. rreg HS (12%bv : bv 5) Qa2.
    rreg HS (13%bv : bv 5) Qa3. rreg HS (21%bv : bv 5) Q21. rreg HS (24%bv : bv 5) Q24.
    rreg HS (25%bv : bv 5) Q25.
    assert (Hsp1 : spZ (ms_regs ms1) = cx_F cx)
      by (unfold spZ; rewrite Qsp; cbn [ew ewset Nat.eqb]; exact U2).
    eassert (HPRE1 : afn_pre tfibsegs B STK_has_prefixed ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ []).
    { eapply (afn_pre_at tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx)
        (cx_W cx) (cx_mem cx) (cx_md cx) [] ly3 S3 W3 (ms_mem ms1) _ EV_names (ms_regs ms1)
        STK_has_prefixed (-224) [] HJ).
      - rewrite Hsp1. lia.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - rewrite Qra. vm_compute. reflexivity.
      - unfold raZ. rewrite Qra. rewrite unsigned_lit_small by lia. lia.
      - rewrite Rc3. exact Hgp.
      - rewrite Rc4. exact Htp.
      - unfold achain. left. split; [right; right|reflexivity].
        unfold s0Z. rewrite Qs0. cbn [ew ewset Nat.eqb]. rewrite E8.
        unfold w64, RD_M1. rewrite unsigned_lit_small by lia. vm_compute. discriminate. }
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
      - rewrite Qa2. cbn [ew ewset Nat.eqb]. exact E34.
      - rewrite Qa3. cbn [ew ewset Nat.eqb]. exact E32.
      - exact Ctc.
      - exact Hcsu.
      - exact Ktc.
      - exact Hcku.
      - exact Hne.
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
    pose proof (g3_ajsub_img_ok B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx)
      (cx_W cx) (cx_mem cx) (cx_md cx) [] ly3 S3 W3 (ms_mem ms1) _ EV_names STK_has_prefixed
      (spZ (ms_regs ms1)) [] [] ly5 S5 W5 mem5 md5 0 HJ HJ5 ltac:(rewrite Hsp1; lia)
      ltac:(rewrite Hsp1; lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ6.
    cbn [app] in HJ6. rewrite Z.add_0_r in HJ6.
    rewrite Hsp1 in HJ5.
    eapply (pl_from_C f cx i d s11 p1 p2 p3 o ly5 S5 W5 regs5 mem5 md5 _ HSEGL HB).
    - split.
      { eapply (pl_mid_hp cx d (cx_v cx + Z.of_nat d + 1) ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _
          ly5 S5 W5 regs5 mem5 md5 IMG HMIDc HJ5 HJ6 Hablk
          ltac:(apply (pl_keeps_sub PL_LOOP PL_KEEP2); [pl_sub | apply (pl_keeps_of_pres PL_KEEP2);
            [exact HP5 | pl_sub]]) HGL5); [|lia|lia].
        rewrite (pl_keeps_of_pres PL_KEEP2 _ _ HP5 ltac:(pl_sub) 9%bv ltac:(cbv [PL_KEEP2 In]; tauto)).
        exact R9c. }
      split; [exact HACC|]. split; [exact Hilt|]. split; [exact HDECL|]. split; [exact HFI|].
      split; [exact Ho|]. split; [exact HFirst|]. split; [exact HLast|]. split; [exact Hall|].
      split; [exact Hd16|].
      split.
      { rewrite (pl_keeps_of_pres PL_CORE _ _ HP5 ltac:(pl_sub) 21%bv ltac:(cbv [PL_CORE In]; tauto)).
        rewrite Q21. cbn [sv_denot ew ewset Nat.eqb]. exact E21. }
      split.
      { rewrite (pl_keeps_of_pres PL_CORE _ _ HP5 ltac:(pl_sub) 24%bv ltac:(cbv [PL_CORE In]; tauto)).
        rewrite Q24. cbn [sv_denot ew ewset Nat.eqb]. pl_num E9. }
      { rewrite (g3_aregs_keep _ _ HP5 25%bv ltac:(cbv [G3_KEPT In]; tauto)).
        rewrite Q25. reflexivity. }
    - exact H10'.
    - reflexivity. } }
Qed.

Lemma pl_from_B : forall f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 vv,
  rd_seg_L B CTX f -> rd_seg_PL B CTX (S f) m -> (length (cx_ub cx) - o - q <= S m)%nat ->
  rd_base B CTX cx ->
  pl_core cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 ->
  getr regs3 25 = w64 (Z.of_nat (length (cx_ub cx) - o)) ->
  getr regs3 26 = w64 (byte_at (cx_ub cx) (o + q)) ->
  getr regs3 10 = w64 vv -> 0 <= vv < 2 ^ 64 ->
  (vv <> 0 <-> is_alnum (byte_at (cx_ub cx) (o + q)) = true) ->
  SRr tfibsegs W3 (cfg_at tfibsegs PL_B regs3 mem3 md3) (rd_post B cx).
Proof.
intros f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 vv HSEGL HSEGPL Hm HB HPL R25 R26 R10 Hvv Hal.
pose proof HPL as HPL0.
pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs. pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (CC & _).
unfold pl_core in HPL. cbv zeta in HPL.
destruct HPL as (HLOOP & HACC & Hilt & HDECL & HFI & Ho & HFirst & HLast & Hqn & HPlainq & HSL & R21 & R22 & R24).
pose proof (pl_mid_of_loop cx d ly3 S3 W3 regs3 mem3 md3 HLOOP) as HMID.
pose proof HMID as (HCOM & R8 & R9 & R18 & R19 & R20 & R23 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof HCOM as (HJ & Hk & R2 & R3 & R4 & R27 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HB as (HAN & HCTX & HROb & H10b & H11b & H12b & Hpresb & Htopr & Hvb & Hv63 & Ctb & Cub & Ktb & Kub &
  Hub255 & Htbmax & HGb & Hlv & Hcntb & Hevb & Hlbb & Hrab & Hchb).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSP : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (FFR : STK_readings = 16624) by reflexivity.
assert (HFlo : alloc_ceiling + 4096 <= cx_F cx) by lia.
assert (HFhi : cx_sp cx + 16 <= 2 ^ 47) by lia.
assert (HF16 : cx_F cx mod 16 = 0)
  by (rewrite HFsp; replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia; rewrite Z_mod_plus_full;
      rewrite HSP; exact Hal16).
pose proof Cu as ((HGu & HNZu) & Hu1 & Hu2 & _).
assert (Hoq : (o + q < length (cx_ub cx))%nat) by lia.
destruct (HGu (o + q)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
rewrite app_nth1 in Vc, Rc by lia.
assert (Hcr : 0 <= byte_at (cx_ub cx) (o + q) < 256) by (unfold byte_at; lia).
pose proof HSLOTS as HSL2. unfold rd_slots_ok in HSL2. cbv [rd_loc_list] in HSL2.
apply Forall_cons_iff in HSL2 as [SL10 HSL2]. apply Forall_cons_iff in HSL2 as [SL18 _].
cbn [fst snd] in SL10, SL18.
pose proof (plB_entry W3 regs3 mem3 (cx_F cx) (byte_at (cx_ub cx) (o + q))
  R2 R27 R26 ltac:(lia) HF16 Hcr (proj1 SL18)) as HS.
set (E := Ereg regs3 ([] : list word)) in *.
assert (E2 : ew E 2 = w64 (cx_F cx)) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); exact R2).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite E2; apply unsigned_lit_small; lia).
assert (E10 : ew E 10 = w64 vv) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl); exact R10).
assert (E25 : ew E 25 = w64 (Z.of_nat (length (cx_ub cx) - o)))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 25 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = w64 (byte_at (cx_ub cx) (o + q)))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 26 26%bv eq_refl); exact R26).
assert (SHOK : sh_ok tfibsegs PL_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 PL_B) mem3 (seg_rom tfibsegs))))) by constructor.
change (unpoison [] mem3) with mem3 in HJ.
unfold cfg_at. change (w64 PL_B) with (Z_to_bv 64 PL_B).
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 PL_B) mem3 (seg_rom tfibsegs))) in HJ.
aj_run_tok rd_tbl_ok HS HJ SHOK PL_Bspan; [pl_awr U2|].
assert (KE0 : forall a, 0 <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha. apply (g3_aview_frame E (ss_mem ss_B) (w_H W3) mem3 (ms_mem ms) HFr a Ha).
  intros (rr & Hin & Hr). cbn [ss_B ss_mem In] in Hin. destruct Hin as [<-|[]].
  cbn [pl_fr_mask YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U2 in Hr. lia. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
  assert (H26a : ew Ex 26 = Z_to_bv 64 (byte_at (cx_ub cx) (o + q))) by (cbn [ew ewset Nat.eqb]; exact E26) end.
srr_branch_tok rd_tbl_ok HS SHOK PL_Bspan.
{ (* isalnum (c) <> 0: the byte is plain *)
  rewrite branch_ne_U, (U_atom E 10 vv E10 Hvv) in Hc. rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  assert (Hpl : plain_ok (byte_at (cx_ub cx) (o + q)) = true) by (apply pl_alnum_plain; apply Hal; exact Hc).
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan PL_P; [pl_awr U2|].
  lazymatch type of HFr0 with frame_of ?Ex ?rs _ _ =>
    assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
    assert (KEs : forall a, 0 <= a < 2 ^ 64 ->
      aview tfibsegs (w_H W3) (ms_mem ms0) a = aview tfibsegs (w_H W3) (ms_mem ms) a) by
      (intros a Ha; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms) (ms_mem ms0) HFr0 a Ha);
       intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin; destruct Hin as [<-|[]];
         cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr; lia);
    clear X2 end.
  assert (KE : forall a, 0 <= a < 2 ^ 64 ->
    aview tfibsegs (w_H W3) (ms_mem ms0) a = aview tfibsegs (w_H W3) mem3 a)
    by (intros a Ha; rewrite (KEs a Ha); exact (KE0 a Ha)).
  assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms0)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
  { apply (g3_val_mem_kept W3 W3 mem3 (ms_mem ms0)); [exact HRP|].
    intros j Hj. cbn in Hj. apply KE; lia. }
  pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 ([] : list word) PL_CORE HS
    ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  rreg HS (13%bv : bv 5) Q13.
  pose proof (pl_core_kept cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 _ (ms_regs ms0) (ms_mem ms0) _
    (cx_F cx) HPL0 HJ ltac:(lia) ltac:(lia) HFlo HFhi ltac:(intros a Ha _; apply KE; lia) KR Vrp) as HC2.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  apply (pl_from_P f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) _
    HSEGL HSEGPL Hm HB HC2); [|exact Hpl].
  rewrite Q13. cbn [sv_denot ew ewset Nat.eqb]. pl_num E25.
}
{ (* isalnum (c) = 0: c - 45 >u 50, then the mask bit *)
  rewrite branch_ne_U, (U_atom E 10 vv E10 Hvv) in Hc. rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  assert (Hnal : is_alnum (byte_at (cx_ub cx) (o + q)) = false).
  { destruct (is_alnum (byte_at (cx_ub cx) (o + q))) eqn:Ea; [|reflexivity].
    exfalso. exact (proj2 Hal eq_refl Hc). }
  aj_run_tok rd_tbl_ok HS HJ SHOK PL_Bspan; [pl_awr U2|].
  lazymatch type of HFr0 with frame_of ?Ex ?rs _ _ =>
    assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
    assert (KEs : forall a, 0 <= a < 2 ^ 64 ->
      aview tfibsegs (w_H W3) (ms_mem ms0) a = aview tfibsegs (w_H W3) (ms_mem ms) a) by
      (intros a Ha; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms) (ms_mem ms0) HFr0 a Ha);
       intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin; destruct Hin as [<-|[]];
         cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr; lia);
    clear X2 end.
  assert (KE01 : forall a, 0 <= a < 2 ^ 64 ->
    aview tfibsegs (w_H W3) (ms_mem ms0) a = aview tfibsegs (w_H W3) mem3 a)
    by (intros a Ha; rewrite (KEs a Ha); exact (KE0 a Ha)).
  srr_branch_tok rd_tbl_ok HS SHOK PL_Bspan.
  { (* c - 45 >u 50: not plain *)
    erewrite (pl_D_of 26 _ (byte_at (cx_ub cx) (o + q)) _ _ _ H26a) in Hc0 by reflexivity.
    pose proof (pl_cls_far _ Hcr Hnal Hc0) as Hnp.
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan PL_N; [pl_awr U2|].
  lazymatch type of HFr1 with frame_of ?Ex ?rs _ _ =>
    assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
    assert (KEt1 : forall a, 0 <= a < 2 ^ 64 ->
      aview tfibsegs (w_H W3) (ms_mem ms1) a = aview tfibsegs (w_H W3) (ms_mem ms0) a) by
      (intros a Ha; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha);
       intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin; destruct Hin as [<-|[]];
         cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr; lia);
    clear X2 end.
    assert (KE : forall a, 0 <= a < 2 ^ 64 ->
    aview tfibsegs (w_H W3) (ms_mem ms1) a = aview tfibsegs (w_H W3) mem3 a)
    by (intros a Ha; rewrite (KEt1 a Ha); exact (KE01 a Ha)).
  assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms1)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
  { apply (g3_val_mem_kept W3 W3 mem3 (ms_mem ms1)); [exact HRP|].
    intros j Hj. cbn in Hj. apply KE; lia. }
  pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 ([] : list word) PL_CORE HS
    ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pose proof (pl_core_kept cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 _ (ms_regs ms1) (ms_mem ms1) _
    (cx_F cx) HPL0 HJ ltac:(lia) ltac:(lia) HFlo HFhi ltac:(intros a Ha _; apply KE; lia) KR Vrp) as HC2.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  exact (pl_from_N f cx i d s11 p1 p2 p3 o q ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ HSEGL HB HC2 Hnp).
  }
  { (* in range: the mask bit decides *)
    erewrite (pl_D_of 26 _ (byte_at (cx_ub cx) (o + q)) _ _ _ H26a) in Hc0 by reflexivity.
    aj_run_tok rd_tbl_ok HS HJ SHOK PL_Bspan; [pl_awr U2|].
  lazymatch type of HFr1 with frame_of ?Ex ?rs _ _ =>
    assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
    assert (KEt1 : forall a, 0 <= a < 2 ^ 64 ->
      aview tfibsegs (w_H W3) (ms_mem ms1) a = aview tfibsegs (w_H W3) (ms_mem ms0) a) by
      (intros a Ha; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha);
       intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin; destruct Hin as [<-|[]];
         cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr; lia);
    clear X2 end.
    assert (KEa : forall a, 0 <= a < 2 ^ 64 ->
    aview tfibsegs (w_H W3) (ms_mem ms1) a = aview tfibsegs (w_H W3) mem3 a)
    by (intros a Ha; rewrite (KEt1 a Ha); exact (KE01 a Ha)).
    lazymatch type of HS with st_ok _ ?Ex _ _ =>
      assert (H26b : ew Ex 26 = Z_to_bv 64 (byte_at (cx_ub cx) (o + q)))
        by (cbn [ew ewset Nat.eqb]; exact E26) end.
    srr_branch_tok rd_tbl_ok HS SHOK PL_Bspan.
    { (* bit clear: not plain *)
      erewrite (pl_D_of 26 _ (byte_at (cx_ub cx) (o + q)) _ _ _ H26b) in Hc1 by reflexivity.
      pose proof (pl_cls_bit0 _ Hcr Hnal Hc0 Hc1) as Hnp.
      aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan PL_N; [pl_awr U2|].
  lazymatch type of HFr2 with frame_of ?Ex ?rs _ _ =>
    assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
    assert (KEt2 : forall a, 0 <= a < 2 ^ 64 ->
      aview tfibsegs (w_H W3) (ms_mem ms2) a = aview tfibsegs (w_H W3) (ms_mem ms1) a) by
      (intros a Ha; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha);
       intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin; destruct Hin as [<-|[]];
         cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr; lia);
    clear X2 end.
      assert (KE : forall a, 0 <= a < 2 ^ 64 ->
    aview tfibsegs (w_H W3) (ms_mem ms2) a = aview tfibsegs (w_H W3) mem3 a)
    by (intros a Ha; rewrite (KEt2 a Ha); exact (KEa a Ha)).
  assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms2)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
  { apply (g3_val_mem_kept W3 W3 mem3 (ms_mem ms2)); [exact HRP|].
    intros j Hj. cbn in Hj. apply KE; lia. }
  pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 ([] : list word) PL_CORE HS
    ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pose proof (pl_core_kept cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 _ (ms_regs ms2) (ms_mem ms2) _
    (cx_F cx) HPL0 HJ ltac:(lia) ltac:(lia) HFlo HFhi ltac:(intros a Ha _; apply KE; lia) KR Vrp) as HC2.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  exact (pl_from_N f cx i d s11 p1 p2 p3 o q ly3 S3 W3 (ms_regs ms2) (ms_mem ms2) _ HSEGL HB HC2 Hnp).
    }
    { (* bit set: plain *)
      erewrite (pl_D_of 26 _ (byte_at (cx_ub cx) (o + q)) _ _ _ H26b) in Hc1 by reflexivity.
      pose proof (pl_cls_bit1 _ Hcr Hnal Hc0 Hc1) as Hpl.
      aj_run_to_tok rd_tbl_ok HS HJ SHOK PL_Bspan PL_P; [pl_awr U2|].
  lazymatch type of HFr2 with frame_of ?Ex ?rs _ _ =>
    assert (X2 : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset Nat.eqb]; exact U2);
    assert (KEt2 : forall a, 0 <= a < 2 ^ 64 ->
      aview tfibsegs (w_H W3) (ms_mem ms2) a = aview tfibsegs (w_H W3) (ms_mem ms1) a) by
      (intros a Ha; apply (g3_aview_frame Ex rs (w_H W3) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha);
       intros (rr & Hin & Hr); cbn [ss_mem add_cond In] in Hin; destruct Hin as [<-|[]];
         cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite X2 in Hr; lia);
    clear X2 end.
      assert (KE : forall a, 0 <= a < 2 ^ 64 ->
    aview tfibsegs (w_H W3) (ms_mem ms2) a = aview tfibsegs (w_H W3) mem3 a)
    by (intros a Ha; rewrite (KEt2 a Ha); exact (KEa a Ha)).
  assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms2)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
  { apply (g3_val_mem_kept W3 W3 mem3 (ms_mem ms2)); [exact HRP|].
    intros j Hj. cbn in Hj. apply KE; lia. }
  pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 ([] : list word) PL_CORE HS
    ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  rreg HS (13%bv : bv 5) Q13.
  pose proof (pl_core_kept cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 _ (ms_regs ms2) (ms_mem ms2) _
    (cx_F cx) HPL0 HJ ltac:(lia) ltac:(lia) HFlo HFhi ltac:(intros a Ha _; apply KE; lia) KR Vrp) as HC2.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  apply (pl_from_P f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 (ms_regs ms2) (ms_mem ms2) _
    HSEGL HSEGPL Hm HB HC2); [|exact Hpl].
  rewrite Q13. cbn [sv_denot ew ewset Nat.eqb]. pl_num E25.
    } } }
Qed.

Lemma pl_from_A2 : forall f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3,
  rd_seg_L B CTX f -> rd_seg_PL B CTX (S f) m -> (length (cx_ub cx) - o - q <= S m)%nat ->
  rd_base B CTX cx ->
  pl_core cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 ->
  getr regs3 25 = w64 (Z.of_nat (length (cx_ub cx) - o)) ->
  getr regs3 10 = w64 (cx_u cx + Z.of_nat o + Z.of_nat q) ->
  SRr tfibsegs W3 (cfg_at tfibsegs PL_A2 regs3 mem3 md3) (rd_post B cx).
Proof.
intros f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 HSEGL HSEGPL Hm HB HPL R25 R10.
pose proof HPL as HPL0.
pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs. pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (CC & _).
unfold pl_core in HPL. cbv zeta in HPL.
destruct HPL as (HLOOP & HACC & Hilt & HDECL & HFI & Ho & HFirst & HLast & Hqn & HPlainq & HSL & R21 & R22 & R24).
pose proof (pl_mid_of_loop cx d ly3 S3 W3 regs3 mem3 md3 HLOOP) as HMID.
pose proof HMID as (HCOM & R8 & R9 & R18 & R19 & R20 & R23 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof HCOM as (HJ & Hk & R2 & R3 & R4 & R27 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HB as (HAN & HCTX & HROb & H10b & H11b & H12b & Hpresb & Htopr & Hvb & Hv63 & Ctb & Cub & Ktb & Kub &
  Hub255 & Htbmax & HGb & Hlv & Hcntb & Hevb & Hlbb & Hrab & Hchb).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARj & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HSP : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (FFR : STK_readings = 16624) by reflexivity.
assert (HFlo : alloc_ceiling + 4096 <= cx_F cx) by lia.
assert (HFhi : cx_sp cx + 16 <= 2 ^ 47) by lia.
assert (HF16 : cx_F cx mod 16 = 0)
  by (rewrite HFsp; replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia; rewrite Z_mod_plus_full;
      rewrite HSP; exact Hal16).
pose proof Cu as ((HGu & HNZu) & Hu1 & Hu2 & _).
assert (Hoq : (o + q < length (cx_ub cx))%nat) by lia.
destruct (HGu (o + q)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
rewrite app_nth1 in Vc, Rc by lia.
assert (Hcr : 0 <= byte_at (cx_ub cx) (o + q) < 256) by (unfold byte_at; lia).
assert (Vc' : val_mem tfibsegs (mrestrict (w_H W3) mem3) (cx_u cx + Z.of_nat o + Z.of_nat q) 1
  (byte_at (cx_ub cx) (o + q))) by (rewrite <- Z.add_assoc, <- Nat2Z.inj_add; exact Vc).
pose proof (plA2_entry W3 regs3 mem3 (cx_u cx + Z.of_nat o + Z.of_nat q) (byte_at (cx_ub cx) (o + q))
  R10 ltac:(lia) Hcr Vc') as HS.
set (E := Ereg regs3 [w64 (byte_at (cx_ub cx) (o + q))]) in *.
assert (E2 : ew E 2 = w64 (cx_F cx)) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); exact R2).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite E2; apply unsigned_lit_small; lia).
assert (E3a : ew E 3 = getr regs3 3) by (unfold E; exact (ew_Ereg_nat regs3 _ 3 3%bv eq_refl)).
assert (E4a : ew E 4 = getr regs3 4) by (unfold E; exact (ew_Ereg_nat regs3 _ 4 4%bv eq_refl)).
assert (E25 : ew E 25 = w64 (Z.of_nat (length (cx_ub cx) - o)))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 25 25%bv eq_refl); exact R25).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = w64 (byte_at (cx_ub cx) (o + q))) by (unfold E; exact (ew_Ereg_extra regs3 _ 0)).
change (unpoison [] mem3) with mem3 in HJ.
unfold cfg_at. change (w64 PL_A2) with (Z_to_bv 64 PL_A2).
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 PL_A2) mem3 (seg_rom tfibsegs))) in HJ.
aj_run rd_tbl_ok HS HJ.
{ awr_ok_tac. }
assert (KE0 : forall a, 0 <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha. apply (g3_aview_frame E (ss_mem ss_A2) (w_H W3) mem3 (ms_mem ms) HFr a Ha).
  intros (rr & Hin & Hr). cbn [ss_A2 ss_mem In] in Hin. destruct Hin as [<-|[]].
  cbn [pl_byte YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
rreg HS (1%bv : bv 5) Qra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp.
rreg HS (10%bv : bv 5) Qa0. rreg HS (26%bv : bv 5) Q26.
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_CORE HS
  ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ [25%bv] HS
  ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR25.
cbn [ms_regs restrict] in KR25.
assert (Hsp1 : spZ (ms_regs ms) = cx_sp cx + 16 + (-224))
  by (unfold spZ; rewrite Qsp; cbn [ew ewset Nat.eqb]; rewrite U2; lia).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ eapply (g3_aj_ro_at B LAWS PC_isalnum STK_RT_ISALNUM
    (fun v => v <> 0 <-> is_alnum (byte_at (cx_ub cx) (o + q)) = true)
    W3 (ms_regs ms) (ms_mem ms) (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx)
    (cx_mem cx) (cx_md cx) [] ly3 S3 _ EV_names (-224) (Z_to_bv 64 PL_B) HJ).
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
assert (KEt : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - 4096 <= a < cx_F cx) ->
  aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) (ms_mem ms) a).
{ intros a Ha Hn. apply Hfr2; [exact Ha|]. unfold STK_RT_ISALNUM, ESTACK. intros Hw. apply Hn. lia. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - 4096 <= a < cx_F cx) ->
  aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha Hn. rewrite (KEt a Ha Hn). apply KE0; lia. }
assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) mem2) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
{ apply (g3_val_mem_kept W3 W3 mem3 mem2); [exact HRP|].
  intros j Hj. cbn in Hj. apply KE; lia. }
assert (HPR2 : pl_keeps PL_CORE regs3 regs2).
{ apply (pl_keeps_trans PL_CORE regs3 (ms_regs ms) regs2); [exact KR|].
  apply (pl_keeps_of_pres PL_CORE); [exact HP2 | pl_sub]. }
pose proof (pl_core_kept cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 regs2 mem2 md2
  (cx_F cx - 4096) HPL0 HJ2 ltac:(lia) ltac:(lia) HFlo HFhi
  ltac:(intros a Ha Hn; apply KE; [lia | unfold pl_win in Hn; lia]) HPR2 Vrp) as HC2.
assert (R25b : getr regs2 25 = w64 (Z.of_nat (length (cx_ub cx) - o))).
{ rewrite (pl_keeps_of_pres [25%bv] _ _ HP2 ltac:(pl_sub) 25%bv ltac:(cbv [In]; tauto)).
  rewrite (KR25 25%bv ltac:(cbv [In]; tauto)). exact R25. }
assert (R26b : getr regs2 26 = w64 (byte_at (cx_ub cx) (o + q))).
{ rewrite (pl_keeps_of_pres [26%bv] _ _ HP2 ltac:(pl_sub) 26%bv ltac:(cbv [In]; tauto)).
  rewrite Q26. cbn [ew ewset Nat.eqb]. exact E32. }
exact (pl_from_B f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs2 mem2 md2 vv HSEGL HSEGPL Hm HB HC2 R25b R26b
  H10v Hvv HR).
Qed.

(* ======== the segment: from plain_local's head, local[q] ======== *)
Theorem rd_PL_holds : forall f m, rd_seg_L B CTX f -> rd_seg_PL B CTX (S f) m -> rd_seg_PL B CTX (S f) (S m).
Proof using IMG ISALNUM HASP.
intros f m HSEGL HSEGPL cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 Hm HB HPL.
pose proof (pl_core_of_PL cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 HPL) as HPL0.
pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs. pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (CC & _).
unfold rd_PL in HPL. cbv zeta in HPL.
destruct HPL as (HLOOP & HACC & Hilt & HDECL & HFI & Ho & HFirst & HLast & Hqn & HPlainq & HSL & R13 & R21 &
  R22 & R24).
pose proof (pl_mid_of_loop cx d ly3 S3 W3 regs3 mem3 md3 HLOOP) as HMID.
pose proof HMID as (HCOM & R8 & R9 & R18 & R19 & R20 & R23 & HSLOTS & HRP & HPERM & HGL & Hcf & Hub & Hwh & Hdle).
pose proof HCOM as (HJ & Hk & R2 & R3 & R4 & R27 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof HB as (HAN & HCTX & HROb & H10b & H11b & H12b & Hpresb & Htopr & Hvb & Hv63 & Ctb & Cub & Ktb & Kub &
  Hub255 & Htbmax & HGb & Hlv & Hcntb & Hevb & Hlbb & Hrab & Hchb).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSP : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (HFsp : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (FFR : STK_readings = 16624) by reflexivity.
assert (HFlo : alloc_ceiling + 4096 <= cx_F cx) by lia.
assert (HFhi : cx_sp cx + 16 <= 2 ^ 47) by lia.
assert (HF16 : cx_F cx mod 16 = 0)
  by (rewrite HFsp; replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia; rewrite Z_mod_plus_full;
      rewrite HSP; exact Hal16).
pose proof Cu as ((HGu & HNZu) & Hu1 & Hu2 & _).
pose proof Cu as (_ & _ & _ & _ & _ & HRAu & _).
assert (Hoq : (o + q < length (cx_ub cx))%nat) by lia.
pose proof HSL as HSL3. unfold rd_slots_ok in HSL3.
apply Forall_cons_iff in HSL3 as [SL08 HSL3]. apply Forall_cons_iff in HSL3 as [SL30 HSL3].
apply Forall_cons_iff in HSL3 as [SL38 HSL3]. apply Forall_cons_iff in HSL3 as [SL40 HSL3].
apply Forall_cons_iff in HSL3 as [SL48 _]. cbn [fst snd] in SL08, SL30, SL38, SL40, SL48.
pose proof (plA_entry W3 regs3 mem3 (cx_F cx) (Z.of_nat q) (cx_u cx + Z.of_nat o)
  R2 R27 R24 ltac:(lia) HF16 ltac:(lia) ltac:(lia) (proj1 SL30) (proj1 SL38) (proj1 SL40)) as HS.
set (E := Ereg regs3 [w64 (cx_u cx + Z.of_nat o); w64 (RD_M1 - (cx_u cx + Z.of_nat o))]) in *.
assert (E2 : ew E 2 = w64 (cx_F cx)) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); exact R2).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite E2; apply unsigned_lit_small; lia).
assert (E13 : ew E 13 = w64 (Z.of_nat (length (cx_ub cx) - o)))
  by (unfold E; rewrite (ew_Ereg_nat regs3 _ 13 13%bv eq_refl); exact R13).
assert (E24 : ew E 24 = w64 (Z.of_nat q)) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 24 24%bv eq_refl); exact R24).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs3 _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = w64 (cx_u cx + Z.of_nat o)) by (unfold E; exact (ew_Ereg_extra regs3 _ 0)).
assert (SHOK : sh_ok tfibsegs PL_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 PL_A) mem3 (seg_rom tfibsegs))))) by constructor.
change (unpoison [] mem3) with mem3 in HJ.
unfold cfg_at. change (w64 RD_PL) with (Z_to_bv 64 PL_A).
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 PL_A) mem3 (seg_rom tfibsegs))) in HJ.
(* the UBSan guard 0x82280 falls by the atom ranges; the shadow check of local + q is the obligation *)
aj_run_tok rd_tbl_ok HS HJ SHOK PL_Bspan; [ | pl_awr U2 | ].
{ lazymatch goal with |- range_addressable (rd_of _ (mrestrict _ ?MM)) (U ?Ex _) _ _ =>
    assert (Y : U Ex (SAlu ALU_ADD (SOff 24 0) (SOff 32 0)) = Z.of_nat q + (cx_u cx + Z.of_nat o)) by
      (apply (pl_U_add Ex 24 32 (Z.of_nat q) (cx_u cx + Z.of_nat o));
        [cbn [ew ewset Nat.eqb]; exact E24 | cbn [ew ewset Nat.eqb]; exact E32 | lia | lia | lia]);
    apply (obl_of_range tfibsegs (w_H W3) MM Ex PL_Bx (U Ex (SAlu ALU_ADD (SOff 24 0) (SOff 32 0))) 1
      (cx_u cx) (Z.of_nat (length (cx_ub cx)) + 1) HRAu);
    [ unfold PL_Bx; apply (U_atom Ex 27 SHADOW_OFF);
        [cbn [ew ewset Nat.eqb]; exact E27 | unfold SHADOW_OFF; lia]
    | rewrite Y; lia | rewrite Y; lia ] end. }
assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha. apply (g3_aview_frame E (ss_mem ss_A) (w_H W3) mem3 (ms_mem ms) HFr a Ha).
  intros (rr & Hin & Hr). cbn [ss_A ss_mem In] in Hin. destruct Hin as [<-|[]].
  cbn [pl_frA YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U2 in Hr. lia. }
assert (Vrp : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (cx_sp cx) 8 (cx_v cx + Z.of_nat d)).
{ apply (g3_val_mem_kept W3 W3 mem3 (ms_mem ms)); [exact HRP|].
  intros j Hj. cbn in Hj. apply KE; lia. }
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs3 _ PL_CORE HS
  ltac:(env_agree_chain (env_agree_refl 32%nat E)) ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pose proof (pl_core_kept cx i d (S f) s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 _ (ms_regs ms) (ms_mem ms) _
  (cx_F cx) HPL0 HJ ltac:(lia) ltac:(lia) HFlo HFhi ltac:(intros a Ha _; apply KE; lia) KR Vrp) as HC2.
rreg HS (25%bv : bv 5) Q25.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  assert (Q10 : getr (ms_regs msX) 10 = sv_denot Ex (SAlu ALU_ADD (SOff 24 0) (SOff 32 0)))
    by (refine (eq_trans (st_ok_restrict_reg tfibsegs _ Ex ssx msX 10%bv HS) _); f_equal; vm_compute; reflexivity);
  assert (Y : U Ex (SAlu ALU_ADD (SOff 24 0) (SOff 32 0)) = Z.of_nat q + (cx_u cx + Z.of_nat o)) by
    (apply (pl_U_add Ex 24 32 (Z.of_nat q) (cx_u cx + Z.of_nat o));
      [cbn [ew ewset Nat.eqb]; exact E24 | cbn [ew ewset Nat.eqb]; exact E32 | lia | lia | lia]) end.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply (pl_from_A2 f m cx i d s11 p1 p2 p3 o q ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ HSEGL HSEGPL Hm HB HC2).
- rewrite Q25. cbn [sv_denot ew ewset Nat.eqb]. pl_num E13.
- rewrite Q10, denot_lit_U, Y. unfold w64. f_equal. lia.
Qed.
End c.
