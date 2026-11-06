(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-10: re-walked from lib/A/Prog/rec_canonical.v (a working branch 1d526f2e737) for
   fuzz_command.asan-ubsan (entry 0x897e8, 115 instructions). The malloc wrapper call and its null/abort edge are one
   program call of xmalloc here (0x89814, PCall CS_xmalloc), taken through cl_callS (PaCall.v) with the statement's
   HXMALLOC at the walk's own fx and HSIG (cmd_sig_prog, CmdObj.v: the call target); s0 holds len there, below
   alloc_ceiling, so achain_low gives xmalloc's frame chain, and xmalloc's journal keeps the frame. The copy loop
   keeps i (a4) and o (a3) and recomputes text + i and out + o per byte; ~out (a2), ~text (a5) and text != 0 (a6)
   feed the UBSan checks. The walk is cut at the xmalloc return (0x89818: the empty-line check), the outer head
   (0x8983c), the word-scan head (0x8984c), the word start (0x8989c), the copy head (0x898d0), the tail (0x89954) and
   the store of the terminator (0x8995c, where the empty line enters). Of the seven UBSan trap branches (to the unimp
   at 0x89988) the executor decides six from the seeds' facts: 0x8985c and 0x89860 from text, text + i >= 4096 (the
   block law), 0x898a4, 0x898d0, 0x898f4 and 0x89954 from ~out, ~text >= 2^64 - 1 - CEIL_MAX and o, i <= LMAX; the
   walk refutes 0x89850 (text + i < text) at the branch, since text + i < 2^64. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_canonical.v, with its module paths and module names changed; 1605 of its 1733 lines of code are new or changed and 2250 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacBoxNameSeg5.v; 6808 of its 6947 lines of code are new or changed and 1594 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacBoxNameLoops.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition p5_regs (i c : Z) : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 15%bv (SLit 3)) 13%bv (SLit 47)) 11%bv (SLit i)) 17%bv (SLit c).
Definition p5_dnreg : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition p5_mem : smem :=
  [ YP09.mkRegion (Some 14%nat) 0 3 0 0
      [YP09.mkChunk 0 (CVal 1 (SLit 32)); YP09.mkChunk 1 (CVal 1 (SLit 40)); YP09.mkChunk 2 (CVal 1 (SLit 0))];
    YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] ].
Definition p5_facts : facts :=
  mkFacts [ (22%nat, mkAF SB SB 0); (14%nat, mkAF IMG_LO IMG_TOP 3);
            (32%nat, mkAF 4096 (2 ^ 47 - 8) 0); (33%nat, mkAF 0 7 0); (16%nat, mkAF 0 47 0) ]
    []
    [ (SAlu ALU_ADD (SOff 20 0) (SOff 16 0), SOff 32 0);
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 14 0) (SLit 3)) (SOff 22 0), SOff 34 0) ].
Definition p5_ss (i c : Z) : sstate :=
  mkSS (AF_reac_box_name + RBN_L5) (p5_regs i c) p5_mem None p5_facts.
Definition P5BX : sv := SOff 22 0.
Definition P5SPAN : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition P5SH : list shent := [ mkSHE 32 0 1 ].
Definition p6_regs (i c : Z) : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 14%bv (SLit 7)) 11%bv (SLit 48))
    23%bv (SLit i)) 16%bv (SLit c).
Definition p6_dnreg : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition p6_mem : smem :=
  [ YP09.mkRegion (Some 9%nat) 120 128 128 128 [YP09.mkChunk 120 (CVal 8 (SOff 35 0))];
    YP09.mkRegion (Some 13%nat) 0 7 0 0
      [YP09.mkChunk 0 (CVal 1 (SLit 32));
       YP09.mkChunk 1 (CVal 1 (SLit 105));
       YP09.mkChunk 2 (CVal 1 (SLit 110));
       YP09.mkChunk 3 (CVal 1 (SLit 32));
       YP09.mkChunk 4 (CVal 1 (SLit 47));
       YP09.mkChunk 5 (CVal 1 (SLit 32));
       YP09.mkChunk 6 (CVal 1 (SLit 0))];
    YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] ].
Definition p6_facts : facts :=
  mkFacts [ (22%nat, mkAF SB SB 0); (13%nat, mkAF IMG_LO IMG_TOP 3);
            (32%nat, mkAF 4096 (2 ^ 47 - 8) 0); (33%nat, mkAF 0 7 0); (15%nat, mkAF 0 47 0);
            (35%nat, mkAF 4096 (2 ^ 47 - 8) 0) ]
    []
    [ (SAlu ALU_ADD (SOff 35 0) (SOff 15 0), SOff 32 0);
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 13 0) (SLit 3)) (SOff 22 0), SOff 34 0) ].
Definition p6_ss (i c : Z) : sstate :=
  mkSS (AF_reac_box_name + RBN_L6) (p6_regs i c) p6_mem None p6_facts.
Definition P6BX : sv := SOff 22 0.
Definition P6SPAN : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition P6SH : list shent := [ mkSHE 32 0 1 ].
Definition P6KEPT : list (bv 5) := [1; 2; 3; 4; 6; 7; 8; 9; 13; 18; 19; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition p7_regs (i c : Z) : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 14%bv (SLit 6)) 11%bv (SLit 48))
    21%bv (SLit i)) 15%bv (SLit c).
Definition p7_dnreg : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition p7_mem : smem :=
  [ YP09.mkRegion (Some 9%nat) 120 128 128 128 [YP09.mkChunk 120 (CVal 8 (SOff 35 0))];
    YP09.mkRegion (Some 13%nat) 0 6 0 0
      [YP09.mkChunk 0 (CVal 1 (SLit 32));
       YP09.mkChunk 1 (CVal 1 (SLit 111));
       YP09.mkChunk 2 (CVal 1 (SLit 117));
       YP09.mkChunk 3 (CVal 1 (SLit 116));
       YP09.mkChunk 4 (CVal 1 (SLit 41));
       YP09.mkChunk 5 (CVal 1 (SLit 0))];
    YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] ].
Definition p7_facts : facts :=
  mkFacts [ (22%nat, mkAF SB SB 0); (13%nat, mkAF IMG_LO IMG_TOP 3);
            (32%nat, mkAF 4096 (2 ^ 47 - 8) 0); (33%nat, mkAF 0 7 0); (23%nat, mkAF 0 47 0);
            (35%nat, mkAF 4096 (2 ^ 47 - 8) 0) ]
    []
    [ (SAlu ALU_ADD (SOff 35 0) (SOff 23 0), SOff 32 0);
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 13 0) (SLit 3)) (SOff 22 0), SOff 34 0) ].
Definition p7_ss (i c : Z) : sstate :=
  mkSS (AF_reac_box_name + RBN_L7) (p7_regs i c) p7_mem None p7_facts.
Definition P7BX : sv := SOff 22 0.
Definition P7SPAN : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition P7SH : list shent := [ mkSHE 32 0 1 ].
Definition P7KEPT : list (bv 5) := [1; 2; 3; 4; 6; 7; 8; 9; 13; 18; 19; 20; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition E5 (regsE : bvmap 5 word) (dn sv sa : Z) : env :=
  Eimg (Ereg regsE (map (Z_to_bv 64) [dn; sv; sa])).
Definition E6 (regsE : bvmap 5 word) (dn sv sa d : Z) : env :=
  Eimg (Ereg regsE (map (Z_to_bv 64) [dn; sv; sa; d])).
Definition E7 (regsE : bvmap 5 word) (dn sv sa d : Z) : env :=
  Eimg (Ereg regsE (map (Z_to_bv 64) [dn; sv; sa; d])).
Lemma p_val_mem_eq : forall (H : word -> bool) (m m' : word -> option byte) a (nn : nat) v,
  (forall x, a <= x < a + Z.of_nat nn -> aview SEGS H m' x = aview SEGS H m x) ->
  val_mem SEGS (mrestrict H m) a nn v -> val_mem SEGS (mrestrict H m') a nn v.
Proof.
intros H m m' a nn v Heq Hv j Hj.
rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat j) (Heq (a + Z.of_nat j) ltac:(lia))).
apply Hv. exact Hj.
Qed.
Lemma p_garr8_eq : forall (H : word -> bool) (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS H m' x = aview SEGS H m x) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
intros H m m' a l Heq Hg j Hj. split; [|exact (proj2 (Hg j Hj))].
apply (p_val_mem_eq H m m' (a + Z.of_nat j) 1 (nth j l 0)).
- intros x Hx. apply Heq. lia.
- exact (proj1 (Hg j Hj)).
Qed.
Lemma p_ra_eq : forall (H : word -> bool) (m m' : word -> option byte) a n,
  (forall x, a <= x < a + n -> aview SEGS H m' (SHADOW_OFF + x / 8) = aview SEGS H m (SHADOW_OFF + x / 8)) ->
  range_addressable (aview SEGS H m) SHADOW_OFF a n ->
  range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof.
intros H m m' a n Heq Hra x Hx. destruct (Hra x Hx) as (s & Hs & Hok).
exists s. split; [|exact Hok]. unfold shadow_of_addr in *. rewrite (Heq x Hx). exact Hs.
Qed.
Lemma p_val_mem1_of_aview : forall (H : word -> bool) (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v /\ 0 <= v < 256.
Proof.
intros H m a v Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; cbn in Hv; [|discriminate].
injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as Hr.
change (bv_modulus 8) with 256 in Hr. split; [|exact Hr].
intros j Hj. assert (Hj0 : (j = 0)%nat) by lia. subst j.
change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small (bv_unsigned b) 256) by lia.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia.
rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma p_rd_aview : forall (H : word -> bool) (m : word -> option byte),
  rd_of SEGS (mrestrict H m) = aview SEGS H m.
Proof. intros H m. reflexivity. Qed.
Lemma p_sh_apart : forall Dv x, in_app Dv 48 -> Dv <= x < Dv + 48 ->
  SHADOW_OFF + x / 8 < Dv \/ Dv + 48 <= SHADOW_OFF + x / 8.
Proof.
intros Dv x [H0 Hz] Hx.
pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma p_dnreg_ok : forall E' (m : word -> option byte) (dn : Z),
  bv_unsigned (ew E' 32) = dn -> 0 <= dn -> dn + 1 <= 2 ^ 64 ->
  writable_at SEGS m dn -> region_ok SEGS E' m p5_dnreg.
Proof.
intros E' m dn H0 H1 H2 Hw. unfold region_ok, p5_dnreg.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H0. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. replace (dn + o) with dn by lia. exact Hw.
Qed.
Lemma p_kept_frame : forall E rs (H : word -> bool) (m m' : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_wrange E rs a -> lo <= a < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' lo hi HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma p_garr8_snoc : forall (H : word -> bool) (m : word -> option byte) a l v,
  garr8 SEGS (mrestrict H m) a l ->
  val_mem SEGS (mrestrict H m) (a + Z.of_nat (length l)) 1 v -> 0 <= v < 256 ->
  garr8 SEGS (mrestrict H m) a (l ++ [v]).
Proof.
intros H m a l v Hg Hv Hr j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length l)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. exact (Hg j Hlt).
- assert (Hje : j = length l) by lia. subst j.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. split; [exact Hv | exact Hr].
Qed.
Ltac p_awr_store E32h dn HBWh :=
  lazymatch goal with
  | |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in
    change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0);
    eapply (awr_ok_cons_gen E0 _ _ stk s0 fp b0 bc ly0 own0 32%nat dn);
      [ reflexivity
      | cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E32h; apply unsigned_lit_small; lia
      | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBWh a ltac:(lia))
      | repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil ]
  end.
Ltac p_awr_ro :=
  lazymatch goal with
  | |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in
    change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0);
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil
  end.
Ltac p_frame HFrh lo hi H1h H2h H3h H4h Kname :=
  pose proof (p_kept_frame _ _ _ _ _ lo hi HFrh
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with
          | In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr
          end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?ew_ewset_other in Hw by lia;
          rewrite ?H1h, ?H2h, ?H3h, ?H4h in Hw; rewrite ?unsigned_lit_small in Hw by lia; lia)) as Kname.
Ltac p_efact HS n En G :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ecur _ _ =>
    lazymatch type of En with
    | ew _ _ = ?v =>
      assert (G : ew Ecur n = v) by
        (cbn [extK]; rewrite ?ew_ewset_other by lia; exact En)
    end
  end.
Ltac p_agree HAE :=
  lazymatch goal with
  | |- env_agree 32 _ (ewset ?X ?m ?v) =>
      apply (env_agree_trans 32 _ X);
      [p_agree HAE | apply (YP03.env_agree_le 32 m); [lia | apply env_agree_ewset]]
  | |- _ => exact HAE
  end.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma p5_entry : forall (fq : YK11.FPState) (W : world SEGS) (regsE : bvmap 5 word) memE
    (i c n ov D s : Z),
  getr regsE 16 = w64 n -> getr regsE 12 = w64 ov -> getr regsE 17 = w64 c ->
  getr regsE 11 = w64 i -> getr regsE 15 = w64 3 -> getr regsE 13 = w64 47 ->
  getr regsE 14 = w64 (VAL (A_OBJ 28)) -> getr regsE 20 = w64 D -> getr regsE 22 = w64 SHADOW_OFF ->
  0 <= i < 8 -> 0 <= c < 256 -> 0 <= n <= 47 ->
  in_app D 48 -> D + 48 <= 2 ^ 63 ->
  VAL (A_OBJ 28) mod 8 = 0 ->
  (VAL (A_OBJ 28) + 3 <= D \/ D + 48 <= VAL (A_OBJ 28)) ->
  garr8 SEGS (mrestrict (w_H W) memE) (VAL (A_OBJ 28)) (rbn_lit5 ++ [0]) ->
  aview SEGS (w_H W) memE (SHADOW_OFF + VAL (A_OBJ 28) / 8) = Some s -> 0 <= s <= 7 ->
  st_ok_pi SEGS VAL (E5 regsE (D + n) s (SHADOW_OFF + VAL (A_OBJ 28) / 8)) (p5_ss i c)
    (restrict (w_H W) (mkst (fx := fq) regsE (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L5))) memE
       (seg_rom SEGS))).
Proof.
intros fq W regsE memE i c n ov D s R16 R12 R17 R11 R15 R13 R14 R20 R22
  Hi Hc Hn Happ H63 Hal HSEP HG HS Hs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 28%nat ltac:(unfold disco_nobj; lia)) as HOB.
unfold IMG_LO, IMG_TOP in HOB.
set (lit := VAL (A_OBJ 28)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
destruct Happ as (HD0 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
assert (HDn : 4096 <= D + n <= 2 ^ 47 - 8) by lia.
rewrite restrict_mkst_fx.
set (E := E5 regsE (D + n) s sa).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + n; s; sa])) m)
  by (intros m Hm; subst E; unfold E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; subst E; unfold E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 (D + n))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 s)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E14 : ew E 14 = Z_to_bv 64 lit) by (rewrite (EE 14%nat 14%bv eq_refl); exact R14).
assert (E16 : ew E 16 = Z_to_bv 64 n) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (E20 : ew E 20 = Z_to_bv 64 D) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
unfold p5_ss, p5_mem, p5_facts. apply pa_entry_st_ok_full.
- apply regs_ok_pin; [| intros X; discriminate X | rewrite R17; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite R11; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite R13; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite R15; cbn [sv_denot]; reflexivity].
  apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 14%nat lit E14) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ lit 0 1 (SLit 32) 32); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r.
      pose proof (proj1 (HG 0%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit5 app nth] in Hb. change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 1 1 (SLit 40) 40); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 1%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit5 app nth] in Hb. change (Z.of_nat 1) with 1 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 2 1 (SLit 0) 0); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 2%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit5 app nth] in Hb. change (Z.of_nat 2) with 2 in Hb. exact Hb.
  + rewrite (VB 34%nat sa E34) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ sa 0 1 (SOff 33 0) s);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r.
    exact (proj1 (p_val_mem1_of_aview (w_H W) memE sa s HS)).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 14%nat lit E14) by lia. rewrite (VB 34%nat sa E34) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E22, unsigned_lit_small by (unfold SHADOW_OFF; lia);
            rewrite Z.pow_0_r, Z.mod_1_r; unfold SB, SHADOW_OFF; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E14, unsigned_lit_small by lia;
            change (2 ^ 3) with 8; unfold IMG_LO, IMG_TOP; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E16, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia | exact I].
  + cbn [f_alias alias_ok]. split; [|split; [|exact I]].
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 20 D E20 ltac:(lia)), (U_atom E 16 n E16 ltac:(lia)),
        (U_atom E 32 (D + n) E32 ltac:(lia)).
      unfold zcanon, M64. apply Z.mod_small. lia.
    * apply (shadow_decl_ok E 14 22 34 lit SHADOW_OFF E14 ltac:(lia) E22).
      rewrite E34. unfold sa. reflexivity.
Qed.


Definition p5_cnt (n0 i : Z) : Z := Z.min (i - 1) (47 - n0).
Definition p5_nn (n0 i : Z) : Z := n0 + p5_cnt n0 i.
Definition p5_ovv (n0 ov0 i : Z) : Z := if n0 + i - 1 <=? 47 then ov0 else 1.
Definition p5_wrl (n0 i : Z) : list Z := firstn (Z.to_nat (p5_cnt n0 i)) rbn_lit5.
Definition P5KEPT : list (bv 5) :=
  [1; 2; 3; 4; 7; 8; 9; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma p6_entry : forall (fq : YK11.FPState) (W : world SEGS) (regsE : bvmap 5 word) memE
    (i c n ov A1 D s : Z),
  getr regsE 15 = w64 n -> getr regsE 12 = w64 ov -> getr regsE 16 = w64 c ->
  getr regsE 23 = w64 i -> getr regsE 14 = w64 7 -> getr regsE 11 = w64 48 ->
  getr regsE 13 = w64 (VAL (A_OBJ 29)) -> getr regsE 9 = w64 A1 ->
  getr regsE 22 = w64 SHADOW_OFF ->
  val_mem SEGS (mrestrict (w_H W) memE) (A1 + 120) 8 D ->
  alloc_ceiling <= A1 + 120 -> A1 + 128 <= 2 ^ 47 ->
  (A1 + 128 <= VAL (A_OBJ 29) \/ VAL (A_OBJ 29) + 7 <= A1 + 120) ->
  (A1 + 128 <= D \/ D + 48 <= A1 + 120) ->
  0 <= i < 8 -> 0 <= c < 256 -> 0 <= n <= 47 ->
  in_app D 48 -> D + 48 <= 2 ^ 63 ->
  VAL (A_OBJ 29) mod 8 = 0 ->
  (VAL (A_OBJ 29) + 7 <= D \/ D + 48 <= VAL (A_OBJ 29)) ->
  garr8 SEGS (mrestrict (w_H W) memE) (VAL (A_OBJ 29)) (rbn_lit6 ++ [0]) ->
  aview SEGS (w_H W) memE (SHADOW_OFF + VAL (A_OBJ 29) / 8) = Some s -> 0 <= s <= 7 ->
  st_ok_pi SEGS VAL (E6 regsE (D + n) s (SHADOW_OFF + VAL (A_OBJ 29) / 8) D) (p6_ss i c)
    (restrict (w_H W) (mkst (fx := fq) regsE (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6))) memE
       (seg_rom SEGS))).
Proof.
intros fq W regsE memE i c n ov A1 D s Rn Rov Rc Ri Rlen Rcap Rlit RA1 RSB RD
  HA1lo HA1hi HA1lit HA1D Hi Hc Hn Happ H63 Hal HSEP HG HS Hs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 29%nat ltac:(unfold disco_nobj; lia)) as HOB.
unfold IMG_LO, IMG_TOP in HOB.
set (lit := VAL (A_OBJ 29)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
destruct Happ as (HD0 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
assert (HDn : 4096 <= D + n <= 2 ^ 47 - 8) by lia.
assert (HDr : 4096 <= D <= 2 ^ 47 - 8) by lia.
rewrite restrict_mkst_fx.
set (E := E6 regsE (D + n) s sa D).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + n; s; sa; D])) m)
  by (intros m Hm; subst E; unfold E6; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; subst E; unfold E6; apply ew_Eimg_Ereg_nat; exact Hm).
assert (Edn : ew E 32 = Z_to_bv 64 (D + n))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (Esv : ew E 33 = Z_to_bv 64 s)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (Esa : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (ED : ew E 35 = Z_to_bv 64 D)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (Elit : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact Rlit).
assert (En : ew E 15 = Z_to_bv 64 n) by (rewrite (EE 15%nat 15%bv eq_refl); exact Rn).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact RA1).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact RSB).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
unfold p6_ss, p6_mem, p6_facts. apply pa_entry_st_ok_full.
- apply regs_ok_pin; [| intros X; discriminate X | rewrite Rc; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite Ri; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite Rcap; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite Rlen; cbn [sv_denot]; reflexivity].
  apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 9%nat A1 E9) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ A1 120 8 (SOff 35 0) D);
      [cbn [sv_denot]; rewrite ED, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    change (N.to_nat 8) with 8%nat. exact RD.
  + rewrite (VB 13%nat lit Elit) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ lit 0 1 (SLit 32) 32); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r.
      pose proof (proj1 (HG 0%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 1 1 (SLit 105) 105); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 1%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 1) with 1 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 2 1 (SLit 110) 110); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 2%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 2) with 2 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 3 1 (SLit 32) 32); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 3%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 3) with 3 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 4 1 (SLit 47) 47); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 4%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 4) with 4 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 5 1 (SLit 32) 32); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 5%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 5) with 5 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 6 1 (SLit 0) 0); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 6%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 6) with 6 in Hb. exact Hb.
  + rewrite (VB 34%nat sa Esa) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ sa 0 1 (SOff 33 0) s);
      [cbn [sv_denot]; rewrite Esv, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r.
    exact (proj1 (p_val_mem1_of_aview (w_H W) memE sa s HS)).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 9%nat A1 E9) by lia. rewrite (VB 13%nat lit Elit) by lia.
  rewrite (VB 34%nat sa Esa) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2];
            rewrite E22, unsigned_lit_small by (unfold SHADOW_OFF; lia);
            rewrite Z.pow_0_r, Z.mod_1_r; unfold SB, SHADOW_OFF; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Elit, unsigned_lit_small by lia;
            change (2 ^ 3) with 8; unfold IMG_LO, IMG_TOP; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Edn, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Esv, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite En, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ED, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia | exact I].
  + cbn [f_alias alias_ok]. split; [|split; [|exact I]].
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 35 D ED ltac:(lia)), (U_atom E 15 n En ltac:(lia)),
        (U_atom E 32 (D + n) Edn ltac:(lia)).
      unfold zcanon, M64. apply Z.mod_small. lia.
    * apply (shadow_decl_ok E 13 22 34 lit SHADOW_OFF Elit ltac:(lia) E22).
      rewrite Esa. unfold sa. reflexivity.
Qed.
Lemma p7_entry : forall (fq : YK11.FPState) (W : world SEGS) (regsE : bvmap 5 word) memE
    (i c n ov A1 D s : Z),
  getr regsE 23 = w64 n -> getr regsE 12 = w64 ov -> getr regsE 15 = w64 c ->
  getr regsE 21 = w64 i -> getr regsE 14 = w64 6 -> getr regsE 11 = w64 48 ->
  getr regsE 13 = w64 (VAL (A_OBJ 30)) -> getr regsE 9 = w64 A1 ->
  getr regsE 22 = w64 SHADOW_OFF ->
  val_mem SEGS (mrestrict (w_H W) memE) (A1 + 120) 8 D ->
  alloc_ceiling <= A1 + 120 -> A1 + 128 <= 2 ^ 47 ->
  (A1 + 128 <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 6 <= A1 + 120) ->
  (A1 + 128 <= D \/ D + 48 <= A1 + 120) ->
  0 <= i < 8 -> 0 <= c < 256 -> 0 <= n <= 47 ->
  in_app D 48 -> D + 48 <= 2 ^ 63 ->
  VAL (A_OBJ 30) mod 8 = 0 ->
  (VAL (A_OBJ 30) + 6 <= D \/ D + 48 <= VAL (A_OBJ 30)) ->
  garr8 SEGS (mrestrict (w_H W) memE) (VAL (A_OBJ 30)) (rbn_lit7 ++ [0]) ->
  aview SEGS (w_H W) memE (SHADOW_OFF + VAL (A_OBJ 30) / 8) = Some s -> 0 <= s <= 7 ->
  st_ok_pi SEGS VAL (E7 regsE (D + n) s (SHADOW_OFF + VAL (A_OBJ 30) / 8) D) (p7_ss i c)
    (restrict (w_H W) (mkst (fx := fq) regsE (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L7))) memE
       (seg_rom SEGS))).
Proof.
intros fq W regsE memE i c n ov A1 D s Rn Rov Rc Ri Rlen Rcap Rlit RA1 RSB RD
  HA1lo HA1hi HA1lit HA1D Hi Hc Hn Happ H63 Hal HSEP HG HS Hs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 30%nat ltac:(unfold disco_nobj; lia)) as HOB.
unfold IMG_LO, IMG_TOP in HOB.
set (lit := VAL (A_OBJ 30)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
destruct Happ as (HD0 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
assert (HDn : 4096 <= D + n <= 2 ^ 47 - 8) by lia.
assert (HDr : 4096 <= D <= 2 ^ 47 - 8) by lia.
rewrite restrict_mkst_fx.
set (E := E7 regsE (D + n) s sa D).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + n; s; sa; D])) m)
  by (intros m Hm; subst E; unfold E7; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; subst E; unfold E7; apply ew_Eimg_Ereg_nat; exact Hm).
assert (Edn : ew E 32 = Z_to_bv 64 (D + n))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (Esv : ew E 33 = Z_to_bv 64 s)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (Esa : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (ED : ew E 35 = Z_to_bv 64 D)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (Elit : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact Rlit).
assert (En : ew E 23 = Z_to_bv 64 n) by (rewrite (EE 23%nat 23%bv eq_refl); exact Rn).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact RA1).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact RSB).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
unfold p7_ss, p7_mem, p7_facts. apply pa_entry_st_ok_full.
- apply regs_ok_pin; [| intros X; discriminate X | rewrite Rc; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite Ri; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite Rcap; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite Rlen; cbn [sv_denot]; reflexivity].
  apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 9%nat A1 E9) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ A1 120 8 (SOff 35 0) D);
      [cbn [sv_denot]; rewrite ED, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    change (N.to_nat 8) with 8%nat. exact RD.
  + rewrite (VB 13%nat lit Elit) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ lit 0 1 (SLit 32) 32); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r.
      pose proof (proj1 (HG 0%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit7 app nth] in Hb. change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 1 1 (SLit 111) 111); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 1%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit7 app nth] in Hb. change (Z.of_nat 1) with 1 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 2 1 (SLit 117) 117); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 2%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit7 app nth] in Hb. change (Z.of_nat 2) with 2 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 3 1 (SLit 116) 116); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 3%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit7 app nth] in Hb. change (Z.of_nat 3) with 3 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 4 1 (SLit 41) 41); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 4%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit7 app nth] in Hb. change (Z.of_nat 4) with 4 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 5 1 (SLit 0) 0); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 5%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit7 app nth] in Hb. change (Z.of_nat 5) with 5 in Hb. exact Hb.
  + rewrite (VB 34%nat sa Esa) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ sa 0 1 (SOff 33 0) s);
      [cbn [sv_denot]; rewrite Esv, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r.
    exact (proj1 (p_val_mem1_of_aview (w_H W) memE sa s HS)).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 9%nat A1 E9) by lia. rewrite (VB 13%nat lit Elit) by lia.
  rewrite (VB 34%nat sa Esa) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2];
            rewrite E22, unsigned_lit_small by (unfold SHADOW_OFF; lia);
            rewrite Z.pow_0_r, Z.mod_1_r; unfold SB, SHADOW_OFF; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Elit, unsigned_lit_small by lia;
            change (2 ^ 3) with 8; unfold IMG_LO, IMG_TOP; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Edn, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Esv, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite En, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ED, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia | exact I].
  + cbn [f_alias alias_ok]. split; [|split; [|exact I]].
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 35 D ED ltac:(lia)), (U_atom E 23 n En ltac:(lia)),
        (U_atom E 32 (D + n) Edn ltac:(lia)).
      unfold zcanon, M64. apply Z.mod_small. lia.
    * apply (shadow_decl_ok E 13 22 34 lit SHADOW_OFF Elit ltac:(lia) E22).
      rewrite Esa. unfold sa. reflexivity.
Qed.
Lemma p_kreg : forall (r1 r2 : bvmap 5 word) (rb : bv 5) (z : Z) v,
  Z_to_bv 5 z = rb -> getr r2 rb = v -> getr r1 rb = v ->
  getr r2 (Z_to_bv 5 z) = getr r1 (Z_to_bv 5 z).
Proof. intros r1 r2 rb z v Hb H2 H1. subst rb. rewrite H2, H1. reflexivity. Qed.
Lemma p5_keep_of : forall (r1 r2 : bvmap 5 word),
  (forall r : bv 5, In r P5KEPT -> getr r2 r = getr r1 r) ->
  getr r2 (Z_to_bv 5 0) = getr r1 (Z_to_bv 5 0) ->
  getr r2 (Z_to_bv 5 13) = getr r1 (Z_to_bv 5 13) ->
  getr r2 (Z_to_bv 5 15) = getr r1 (Z_to_bv 5 15) ->
  rbn_keep_regs r1 r2 [5; 6; 10; 11; 12; 16; 17].
Proof.
intros r1 r2 H H0 H13 H15 z Hz Hnin.
assert (Hc : z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9 \/
  z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19 \/
  z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29 \/
  z = 30 \/ z = 31) by lia.
repeat (destruct Hc as [-> | Hc]); try subst z;
  first [ solve [exfalso; apply Hnin; cbn [In]; repeat first [left; reflexivity | right]]
        | exact H0 | exact H13 | exact H15
        | solve [apply H; unfold P5KEPT; cbn [In];
                 repeat first [left; apply bv_eq; vm_compute; reflexivity | right]] ].
Qed.
Lemma p6_keep_of : forall (r1 r2 : bvmap 5 word),
  (forall r : bv 5, In r P6KEPT -> getr r2 r = getr r1 r) ->
  getr r2 (Z_to_bv 5 0) = getr r1 (Z_to_bv 5 0) ->
  getr r2 (Z_to_bv 5 11) = getr r1 (Z_to_bv 5 11) ->
  getr r2 (Z_to_bv 5 14) = getr r1 (Z_to_bv 5 14) ->
  rbn_keep_regs r1 r2 [5; 10; 12; 15; 16; 17; 23].
Proof.
intros r1 r2 H H0 H13 H15 z Hz Hnin.
assert (Hc : z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9 \/
  z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19 \/
  z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29 \/
  z = 30 \/ z = 31) by lia.
repeat (destruct Hc as [-> | Hc]); try subst z;
  first [ solve [exfalso; apply Hnin; cbn [In]; repeat first [left; reflexivity | right]]
        | exact H0 | exact H13 | exact H15
        | solve [apply H; unfold P6KEPT; cbn [In];
                 repeat first [left; apply bv_eq; vm_compute; reflexivity | right]] ].
Qed.
Lemma p7_keep_of : forall (r1 r2 : bvmap 5 word),
  (forall r : bv 5, In r P7KEPT -> getr r2 r = getr r1 r) ->
  getr r2 (Z_to_bv 5 0) = getr r1 (Z_to_bv 5 0) ->
  getr r2 (Z_to_bv 5 11) = getr r1 (Z_to_bv 5 11) ->
  getr r2 (Z_to_bv 5 14) = getr r1 (Z_to_bv 5 14) ->
  rbn_keep_regs r1 r2 [5; 10; 12; 15; 16; 17; 21; 23].
Proof.
intros r1 r2 H H0 H13 H15 z Hz Hnin.
assert (Hc : z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9 \/
  z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19 \/
  z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29 \/
  z = 30 \/ z = 31) by lia.
repeat (destruct Hc as [-> | Hc]); try subst z;
  first [ solve [exfalso; apply Hnin; cbn [In]; repeat first [left; reflexivity | right]]
        | exact H0 | exact H13 | exact H15
        | solve [apply H; unfold P7KEPT; cbn [In];
                 repeat first [left; apply bv_eq; vm_compute; reflexivity | right]] ].
Qed.
Section S5.
Context (fq : YK11.FPState).
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (D n0 ov0 : Z).
Hypothesis HSRC : rbn_lsrc W memc (VAL (A_OBJ 28)) (rbn_lit5 ++ [0]).
Hypothesis HAL : VAL (A_OBJ 28) mod 8 = 0.
Hypothesis HBUF : rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc D 48.
Hypothesis HSEP : VAL (A_OBJ 28) + 3 <= D \/ D + 48 <= VAL (A_OBJ 28).
Hypothesis HN0 : 0 <= n0 <= 47.
Hypothesis HOV0 : ov0 = 0 \/ ov0 = 1.
Definition p5_pkg (i : Z) (regsE : bvmap 5 word) (memE : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + Z.of_nat (length (p5_wrl n0 i))) ->
     aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a) /\
  garr8 SEGS (mrestrict (w_H W) memE) (D + n0) (p5_wrl n0 i) /\
  (forall a, D <= a < D + 48 -> apresent (w_H W) memE a) /\
  rbn_keep_regs regs regsE [5; 6; 10; 11; 12; 16; 17] /\
  getr regsE 16 = w64 (p5_nn n0 i) /\ getr regsE 12 = w64 (p5_ovv n0 ov0 i) /\
  getr regsE 17 = w64 (nth (Z.to_nat (i - 1)) rbn_lit5 0) /\
  getr regsE 11 = w64 i /\ getr regsE 15 = w64 3 /\ getr regsE 13 = w64 47 /\
  getr regsE 14 = w64 (VAL (A_OBJ 28)) /\ getr regsE 20 = w64 D /\ getr regsE 22 = w64 SHADOW_OFF.
Definition p5_next (i : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = cfg_at (fx := fq) SEGS (BASE + (if i <=? 2 then 15684 else 15792)) regs2 mem2 md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ p5_pkg i regs2 mem2.
Definition p5_stmt (i : Z) : Prop :=
  forall (regsE : bvmap 5 word) memE mdE,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k ->
  p5_pkg i regsE memE ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L5) regsE memE mdE) (p5_next (i + 1)).
Lemma p5_it2 : p5_stmt 2.
Proof.
unfold p5_stmt, p5_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & R16 & R12 & R17 & R11 & R15 & R13 & R14 & R20 & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 28%nat ltac:(unfold disco_nobj; lia)) as HOB. unfold IMG_LO, IMG_TOP in HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 28)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit5 ++ [0])) = 3) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p5_wrl n0 2)) = p5_cnt n0 2)
  by (unfold p5_wrl, p5_cnt; rewrite firstn_length; cbn [length rbn_lit5]; lia).
assert (Hc2 : 0 <= p5_cnt n0 2 <= 1) by (unfold p5_cnt; lia).
assert (HnB : p5_nn n0 2 = n0 + p5_cnt n0 2) by reflexivity.
assert (HnR : 0 <= p5_nn n0 2 <= 47) by (unfold p5_nn, p5_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p5_cnt n0 2) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 3).
{ apply (p_ra_eq (w_H W) memc memE lit 3); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit5 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit5 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
destruct (HRA2 (lit + 2) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 2) mod 8 = 2)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 2) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (2 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 2 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (R17' : getr regsE 17 = w64 40) by (cbn in R17; exact R17).
pose proof (p5_entry fq W regsE memE 2 40 (p5_nn n0 2) (p5_ovv n0 ov0 2) D sv
  R16 R12 R17' R11 R15 R13 R14 R20 R22 ltac:(lia) ltac:(lia) HnR HAPP HD63 HAL HSEP HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := E5 regsE (D + p5_nn n0 2) sv sa) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E5; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D + p5_nn n0 2; sv; sa])) E)
  by (unfold E, E5; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + p5_nn n0 2; sv; sa])) m)
  by (intros m Hm; unfold E, E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 (D + p5_nn n0 2))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U32 : U E (SOff 32 0) = D + p5_nn n0 2) by (apply (U_atom E 32 _ E32); lia).
assert (U22 : U E P5BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P5BX P5SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P5SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U32, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U32, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L5)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L5)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P5SPAN.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
  ltac:(intros a (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K1.
rename HG into HG1. clear HF HFr.
assert (E16 : ew E 16 = Z_to_bv 64 (p5_nn n0 2)) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (B32 : bv_unsigned (ew E 32) = D + p5_nn n0 2) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E14 : ew E 14 = Z_to_bv 64 lit) by (rewrite (EE 14%nat 14%bv eq_refl); exact R14).
assert (B14 : bv_unsigned (ew E 14) = lit) by (rewrite E14; apply unsigned_lit_small; lia).
assert (E34 : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (B34 : bv_unsigned (ew E 34) = sa) by (rewrite E34; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK P5SPAN.
- rewrite branch_ltu_U in Hc. rewrite (U_lit E 47) in Hc by lia.
  rewrite (U_atom_off E 16 (p5_nn n0 2) 1 E16) in Hc by lia.
  apply Z.ltb_lt in Hc.
  assert (Hn47 : p5_nn n0 2 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P5SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P5SPAN.
  +
    p_efact HS 33%nat E33 G33.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv G33) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 3 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G33, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P5SPAN (AF_reac_box_name + RBN_L5X).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 E32 E14 E34 E34 K3. rename HG into HG3. clear HF HFr.
    prreg HS (16%bv : bv 5) Q16. prreg HS (12%bv : bv 5) Q12. prreg HS (17%bv : bv 5) Q17.
    prreg HS (11%bv : bv 5) Q11. prreg HS (15%bv : bv 5) Q15. prreg HS (13%bv : bv 5) Q13.
    prreg HS (14%bv : bv 5) Q14. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P5KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 6; 10; 11; 12; 16; 17]) by
        (apply p5_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (13%bv : bv 5) 13 (Z_to_bv 64 47)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q13 R13)
         | apply (p_kreg _ _ (15%bv : bv 5) 15 (Z_to_bv 64 3)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q15 R15) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p5_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p5_nn n0 3 = p5_nn n0 2) by (unfold p5_nn, p5_cnt in *; lia).
    assert (Hw3 : p5_wrl n0 3 = p5_wrl n0 2) by (unfold p5_wrl, p5_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p5_ovv n0 ov0 3 = 1).
    { unfold p5_ovv. replace (n0 + 3 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p5_nn, p5_cnt in Hn47; lia]. }
    change (2 + 1) with 3. unfold p5_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p5_wrl n0 2)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q16, E16; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q17; cbn [rbn_lit5 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q15; reflexivity|].
    split; [rewrite Q13; reflexivity|].
    split; [rewrite Q14, E14; reflexivity|].
    split; [rewrite Q20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P5SPAN (AF_reac_box_name + RBN_L5X).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 E32 E14 E34 E34 K3. rename HG into HG3. clear HF HFr.
    prreg HS (16%bv : bv 5) Q16. prreg HS (12%bv : bv 5) Q12. prreg HS (17%bv : bv 5) Q17.
    prreg HS (11%bv : bv 5) Q11. prreg HS (15%bv : bv 5) Q15. prreg HS (13%bv : bv 5) Q13.
    prreg HS (14%bv : bv 5) Q14. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P5KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 6; 10; 11; 12; 16; 17]) by
        (apply p5_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (13%bv : bv 5) 13 (Z_to_bv 64 47)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q13 R13)
         | apply (p_kreg _ _ (15%bv : bv 5) 15 (Z_to_bv 64 3)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q15 R15) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p5_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p5_nn n0 3 = p5_nn n0 2) by (unfold p5_nn, p5_cnt in *; lia).
    assert (Hw3 : p5_wrl n0 3 = p5_wrl n0 2) by (unfold p5_wrl, p5_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p5_ovv n0 ov0 3 = 1).
    { unfold p5_ovv. replace (n0 + 3 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p5_nn, p5_cnt in Hn47; lia]. }
    change (2 + 1) with 3. unfold p5_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p5_wrl n0 2)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q16, E16; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q17; cbn [rbn_lit5 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q15; reflexivity|].
    split; [rewrite Q13; reflexivity|].
    split; [rewrite Q14, E14; reflexivity|].
    split; [rewrite Q20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    rewrite Q22, E22. reflexivity.

- rewrite branch_ltu_U in Hc. rewrite (U_lit E 47) in Hc by lia.
  rewrite (U_atom_off E 16 (p5_nn n0 2) 1 E16) in Hc by lia.
  apply Z.ltb_ge in Hc.
  assert (Hn46 : p5_nn n0 2 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p5_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p5_nn n0 2) B32 ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p5_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p5_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B32, B14, B34;
          repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P5SPAN.
  {     lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_gen E _ _ STK sp0 FP _ _ lyc own 32%nat (D + p5_nn n0 2));
      [reflexivity | exact B32 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBW a ltac:(lia)) |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p5_nn n0 2) (D + p5_nn n0 2 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?B32, ?B14, ?B34 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P5SPAN.
  +
    p_efact HS 33%nat E33 G33.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv G33) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 3 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G33, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P5SPAN (AF_reac_box_name + RBN_L5X).
    { p_awr_store E32 (D + p5_nn n0 2) HBW. }
    p_frame HFr (D + p5_nn n0 2) (D + p5_nn n0 2 + 1) E32 E14 E34 E34 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p5_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p5_nn n0 2) _ 0 1 0 1 0 1%N (SLit 40) 40 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (16%bv : bv 5) Q16. prreg HS (12%bv : bv 5) Q12. prreg HS (17%bv : bv 5) Q17.
    prreg HS (11%bv : bv 5) Q11. prreg HS (15%bv : bv 5) Q15. prreg HS (13%bv : bv 5) Q13.
    prreg HS (14%bv : bv 5) Q14. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P5KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 6; 10; 11; 12; 16; 17]) by
        (apply p5_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (13%bv : bv 5) 13 (Z_to_bv 64 47)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q13 R13)
         | apply (p_kreg _ _ (15%bv : bv 5) 15 (Z_to_bv 64 3)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q15 R15) ]) end.
    assert (Hc2e : p5_cnt n0 2 = 1) by (unfold p5_nn, p5_cnt in *; lia).
    assert (Hc3e : p5_cnt n0 3 = 2) by (unfold p5_nn, p5_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p5_wrl n0 3)) = p5_cnt n0 3)
      by (unfold p5_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit5]; lia).
    assert (Hn3 : p5_nn n0 3 = p5_nn n0 2 + 1) by (unfold p5_nn; lia).
    assert (Ho3 : p5_ovv n0 ov0 3 = p5_ovv n0 ov0 2).
    { unfold p5_ovv.
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p5_nn, p5_cnt in *; lia).
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p5_nn, p5_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p5_wrl n0 3 = p5_wrl n0 2 ++ [40]).
    { unfold p5_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p5_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (2 + 1) with 3. unfold p5_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p5_nn, p5_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p5_nn, p5_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p5_nn, p5_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p5_wrl n0 2)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p5_nn, p5_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p5_nn, p5_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 1) with (D + p5_nn n0 2) by (unfold p5_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q16, E16, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q17; cbn [rbn_lit5 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q15; reflexivity|].
    split; [rewrite Q13; reflexivity|].
    split; [rewrite Q14, E14; reflexivity|].
    split; [rewrite Q20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P5SPAN (AF_reac_box_name + RBN_L5X).
    { p_awr_store E32 (D + p5_nn n0 2) HBW. }
    p_frame HFr (D + p5_nn n0 2) (D + p5_nn n0 2 + 1) E32 E14 E34 E34 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p5_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p5_nn n0 2) _ 0 1 0 1 0 1%N (SLit 40) 40 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (16%bv : bv 5) Q16. prreg HS (12%bv : bv 5) Q12. prreg HS (17%bv : bv 5) Q17.
    prreg HS (11%bv : bv 5) Q11. prreg HS (15%bv : bv 5) Q15. prreg HS (13%bv : bv 5) Q13.
    prreg HS (14%bv : bv 5) Q14. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P5KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 6; 10; 11; 12; 16; 17]) by
        (apply p5_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (13%bv : bv 5) 13 (Z_to_bv 64 47)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q13 R13)
         | apply (p_kreg _ _ (15%bv : bv 5) 15 (Z_to_bv 64 3)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q15 R15) ]) end.
    assert (Hc2e : p5_cnt n0 2 = 1) by (unfold p5_nn, p5_cnt in *; lia).
    assert (Hc3e : p5_cnt n0 3 = 2) by (unfold p5_nn, p5_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p5_wrl n0 3)) = p5_cnt n0 3)
      by (unfold p5_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit5]; lia).
    assert (Hn3 : p5_nn n0 3 = p5_nn n0 2 + 1) by (unfold p5_nn; lia).
    assert (Ho3 : p5_ovv n0 ov0 3 = p5_ovv n0 ov0 2).
    { unfold p5_ovv.
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p5_nn, p5_cnt in *; lia).
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p5_nn, p5_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p5_wrl n0 3 = p5_wrl n0 2 ++ [40]).
    { unfold p5_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p5_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (2 + 1) with 3. unfold p5_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p5_nn, p5_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p5_nn, p5_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p5_nn, p5_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p5_wrl n0 2)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p5_nn, p5_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p5_nn, p5_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 1) with (D + p5_nn n0 2) by (unfold p5_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q16, E16, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q17; cbn [rbn_lit5 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q15; reflexivity|].
    split; [rewrite Q13; reflexivity|].
    split; [rewrite Q14, E14; reflexivity|].
    split; [rewrite Q20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    rewrite Q22, E22. reflexivity.

Qed.
Lemma p5_it1 : p5_stmt 1.
Proof.
unfold p5_stmt, p5_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & R16 & R12 & R17 & R11 & R15 & R13 & R14 & R20 & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 28%nat ltac:(unfold disco_nobj; lia)) as HOB. unfold IMG_LO, IMG_TOP in HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 28)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit5 ++ [0])) = 3) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p5_wrl n0 1)) = p5_cnt n0 1)
  by (unfold p5_wrl, p5_cnt; rewrite firstn_length; cbn [length rbn_lit5]; lia).
assert (Hc2 : 0 <= p5_cnt n0 1 <= 0) by (unfold p5_cnt; lia).
assert (HnB : p5_nn n0 1 = n0 + p5_cnt n0 1) by reflexivity.
assert (HnR : 0 <= p5_nn n0 1 <= 47) by (unfold p5_nn, p5_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p5_cnt n0 1) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 3).
{ apply (p_ra_eq (w_H W) memc memE lit 3); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit5 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit5 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
destruct (HRA2 (lit + 1) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 1) mod 8 = 1)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 1) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (1 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 1 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (R17' : getr regsE 17 = w64 32) by (cbn in R17; exact R17).
pose proof (p5_entry fq W regsE memE 1 32 (p5_nn n0 1) (p5_ovv n0 ov0 1) D sv
  R16 R12 R17' R11 R15 R13 R14 R20 R22 ltac:(lia) ltac:(lia) HnR HAPP HD63 HAL HSEP HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := E5 regsE (D + p5_nn n0 1) sv sa) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E5; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D + p5_nn n0 1; sv; sa])) E)
  by (unfold E, E5; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + p5_nn n0 1; sv; sa])) m)
  by (intros m Hm; unfold E, E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 (D + p5_nn n0 1))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U32 : U E (SOff 32 0) = D + p5_nn n0 1) by (apply (U_atom E 32 _ E32); lia).
assert (U22 : U E P5BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P5BX P5SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P5SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U32, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U32, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L5)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L5)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P5SPAN.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
  ltac:(intros a (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K1.
rename HG into HG1. clear HF HFr.
assert (E16 : ew E 16 = Z_to_bv 64 (p5_nn n0 1)) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (B32 : bv_unsigned (ew E 32) = D + p5_nn n0 1) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E14 : ew E 14 = Z_to_bv 64 lit) by (rewrite (EE 14%nat 14%bv eq_refl); exact R14).
assert (B14 : bv_unsigned (ew E 14) = lit) by (rewrite E14; apply unsigned_lit_small; lia).
assert (E34 : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (B34 : bv_unsigned (ew E 34) = sa) by (rewrite E34; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK P5SPAN.
- rewrite branch_ltu_U in Hc. rewrite (U_lit E 47) in Hc by lia.
  rewrite (U_atom_off E 16 (p5_nn n0 1) 1 E16) in Hc by lia.
  apply Z.ltb_lt in Hc.
  assert (Hn47 : p5_nn n0 1 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P5SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
psrr_branch_tok RUN BR HS SHOK P5SPAN.
  +
    p_efact HS 33%nat E33 G33.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv G33) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 2 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G33, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
paj_run_to_tok RUNTO HS HJ SHOK P5SPAN (AF_reac_box_name + RBN_L5).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 E32 E14 E34 E34 K3. rename HG into HG3. clear HF HFr.
    prreg HS (16%bv : bv 5) Q16. prreg HS (12%bv : bv 5) Q12. prreg HS (17%bv : bv 5) Q17.
    prreg HS (11%bv : bv 5) Q11. prreg HS (15%bv : bv 5) Q15. prreg HS (13%bv : bv 5) Q13.
    prreg HS (14%bv : bv 5) Q14. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P5KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 6; 10; 11; 12; 16; 17]) by
        (apply p5_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (13%bv : bv 5) 13 (Z_to_bv 64 47)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q13 R13)
         | apply (p_kreg _ _ (15%bv : bv 5) 15 (Z_to_bv 64 3)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q15 R15) ]) end.
pmkst HS.
apply SRr_ret. unfold p5_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p5_nn n0 2 = p5_nn n0 1) by (unfold p5_nn, p5_cnt in *; lia).
    assert (Hw3 : p5_wrl n0 2 = p5_wrl n0 1) by (unfold p5_wrl, p5_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p5_ovv n0 ov0 2 = 1).
    { unfold p5_ovv. replace (n0 + 2 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p5_nn, p5_cnt in Hn47; lia]. }
    change (1 + 1) with 2. unfold p5_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p5_wrl n0 1)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
split; [rewrite Q16, E16; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q17; cbn [rbn_lit5 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q15; reflexivity|].
    split; [rewrite Q13; reflexivity|].
    split; [rewrite Q14, E14; reflexivity|].
    split; [rewrite Q20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    rewrite Q22, E22. reflexivity.
  +
paj_run_to_tok RUNTO HS HJ SHOK P5SPAN (AF_reac_box_name + RBN_L5).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 E32 E14 E34 E34 K3. rename HG into HG3. clear HF HFr.
    prreg HS (16%bv : bv 5) Q16. prreg HS (12%bv : bv 5) Q12. prreg HS (17%bv : bv 5) Q17.
    prreg HS (11%bv : bv 5) Q11. prreg HS (15%bv : bv 5) Q15. prreg HS (13%bv : bv 5) Q13.
    prreg HS (14%bv : bv 5) Q14. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P5KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 6; 10; 11; 12; 16; 17]) by
        (apply p5_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (13%bv : bv 5) 13 (Z_to_bv 64 47)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q13 R13)
         | apply (p_kreg _ _ (15%bv : bv 5) 15 (Z_to_bv 64 3)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q15 R15) ]) end.
pmkst HS.
apply SRr_ret. unfold p5_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p5_nn n0 2 = p5_nn n0 1) by (unfold p5_nn, p5_cnt in *; lia).
    assert (Hw3 : p5_wrl n0 2 = p5_wrl n0 1) by (unfold p5_wrl, p5_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p5_ovv n0 ov0 2 = 1).
    { unfold p5_ovv. replace (n0 + 2 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p5_nn, p5_cnt in Hn47; lia]. }
    change (1 + 1) with 2. unfold p5_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p5_wrl n0 1)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
split; [rewrite Q16, E16; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q17; cbn [rbn_lit5 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q15; reflexivity|].
    split; [rewrite Q13; reflexivity|].
    split; [rewrite Q14, E14; reflexivity|].
    split; [rewrite Q20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    rewrite Q22, E22. reflexivity.

- rewrite branch_ltu_U in Hc. rewrite (U_lit E 47) in Hc by lia.
  rewrite (U_atom_off E 16 (p5_nn n0 1) 1 E16) in Hc by lia.
  apply Z.ltb_ge in Hc.
  assert (Hn46 : p5_nn n0 1 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p5_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p5_nn n0 1) B32 ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p5_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p5_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B32, B14, B34;
          repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P5SPAN.
  {     lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_gen E _ _ STK sp0 FP _ _ lyc own 32%nat (D + p5_nn n0 1));
      [reflexivity | exact B32 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBW a ltac:(lia)) |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p5_nn n0 1) (D + p5_nn n0 1 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?B32, ?B14, ?B34 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
psrr_branch_tok RUN BR HS SHOK P5SPAN.
  +
    p_efact HS 33%nat E33 G33.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv G33) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 2 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G33, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
paj_run_to_tok RUNTO HS HJ SHOK P5SPAN (AF_reac_box_name + RBN_L5).
    { p_awr_store E32 (D + p5_nn n0 1) HBW. }
    p_frame HFr (D + p5_nn n0 1) (D + p5_nn n0 1 + 1) E32 E14 E34 E34 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p5_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p5_nn n0 1) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (16%bv : bv 5) Q16. prreg HS (12%bv : bv 5) Q12. prreg HS (17%bv : bv 5) Q17.
    prreg HS (11%bv : bv 5) Q11. prreg HS (15%bv : bv 5) Q15. prreg HS (13%bv : bv 5) Q13.
    prreg HS (14%bv : bv 5) Q14. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P5KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 6; 10; 11; 12; 16; 17]) by
        (apply p5_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (13%bv : bv 5) 13 (Z_to_bv 64 47)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q13 R13)
         | apply (p_kreg _ _ (15%bv : bv 5) 15 (Z_to_bv 64 3)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q15 R15) ]) end.
    assert (Hc2e : p5_cnt n0 1 = 0) by (unfold p5_nn, p5_cnt in *; lia).
    assert (Hc3e : p5_cnt n0 2 = 1) by (unfold p5_nn, p5_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p5_wrl n0 2)) = p5_cnt n0 2)
      by (unfold p5_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit5]; lia).
    assert (Hn3 : p5_nn n0 2 = p5_nn n0 1 + 1) by (unfold p5_nn; lia).
    assert (Ho3 : p5_ovv n0 ov0 2 = p5_ovv n0 ov0 1).
    { unfold p5_ovv.
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p5_nn, p5_cnt in *; lia).
      replace (n0 + 1 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p5_nn, p5_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p5_wrl n0 2 = p5_wrl n0 1 ++ [32]).
    { unfold p5_wrl. rewrite Hc2e, Hc3e. reflexivity. }
pmkst HS.
apply SRr_ret. unfold p5_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (1 + 1) with 2. unfold p5_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p5_nn, p5_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p5_nn, p5_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p5_nn, p5_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p5_wrl n0 1)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p5_nn, p5_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p5_nn, p5_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 0) with (D + p5_nn n0 1) by (unfold p5_nn, p5_cnt; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
split; [rewrite Q16, E16, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q17; cbn [rbn_lit5 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q15; reflexivity|].
    split; [rewrite Q13; reflexivity|].
    split; [rewrite Q14, E14; reflexivity|].
    split; [rewrite Q20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    rewrite Q22, E22. reflexivity.
  +
paj_run_to_tok RUNTO HS HJ SHOK P5SPAN (AF_reac_box_name + RBN_L5).
    { p_awr_store E32 (D + p5_nn n0 1) HBW. }
    p_frame HFr (D + p5_nn n0 1) (D + p5_nn n0 1 + 1) E32 E14 E34 E34 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p5_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p5_nn n0 1) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (16%bv : bv 5) Q16. prreg HS (12%bv : bv 5) Q12. prreg HS (17%bv : bv 5) Q17.
    prreg HS (11%bv : bv 5) Q11. prreg HS (15%bv : bv 5) Q15. prreg HS (13%bv : bv 5) Q13.
    prreg HS (14%bv : bv 5) Q14. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P5KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 6; 10; 11; 12; 16; 17]) by
        (apply p5_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (13%bv : bv 5) 13 (Z_to_bv 64 47)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q13 R13)
         | apply (p_kreg _ _ (15%bv : bv 5) 15 (Z_to_bv 64 3)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q15 R15) ]) end.
    assert (Hc2e : p5_cnt n0 1 = 0) by (unfold p5_nn, p5_cnt in *; lia).
    assert (Hc3e : p5_cnt n0 2 = 1) by (unfold p5_nn, p5_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p5_wrl n0 2)) = p5_cnt n0 2)
      by (unfold p5_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit5]; lia).
    assert (Hn3 : p5_nn n0 2 = p5_nn n0 1 + 1) by (unfold p5_nn; lia).
    assert (Ho3 : p5_ovv n0 ov0 2 = p5_ovv n0 ov0 1).
    { unfold p5_ovv.
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p5_nn, p5_cnt in *; lia).
      replace (n0 + 1 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p5_nn, p5_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p5_wrl n0 2 = p5_wrl n0 1 ++ [32]).
    { unfold p5_wrl. rewrite Hc2e, Hc3e. reflexivity. }
pmkst HS.
apply SRr_ret. unfold p5_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (1 + 1) with 2. unfold p5_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p5_nn, p5_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p5_nn, p5_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p5_nn, p5_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p5_wrl n0 1)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p5_nn, p5_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p5_nn, p5_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 0) with (D + p5_nn n0 1) by (unfold p5_nn, p5_cnt; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
split; [rewrite Q16, E16, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q17; cbn [rbn_lit5 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q15; reflexivity|].
    split; [rewrite Q13; reflexivity|].
    split; [rewrite Q14, E14; reflexivity|].
    split; [rewrite Q20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    rewrite Q22, E22. reflexivity.

Qed.
Lemma p5_all : forall (regsE : bvmap 5 word) memE mdE,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k ->
  p5_pkg 1 regsE memE ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L5) regsE memE mdE) (p5_next 3).
Proof.
intros regsE memE mdE HJ HP.
eapply SRr_bind; [exact (p5_it1 regsE memE mdE HJ HP)|].
intros W' c' Hle Hx. change (1 + 1) with 2 in Hx.
destruct Hx as (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2).
assert (Hpc5 : (if (2 : Z) <=? 2 then 15684 else 15792) = AF_reac_box_name + RBN_L5) by reflexivity.
rewrite Hpc5.
replace (BASE + (AF_reac_box_name + RBN_L5)) with (BASE + AF_reac_box_name + RBN_L5) by lia.
pose proof (p5_it2 regs2 mem2 md2 HJ2 HP2) as HR. change (2 + 1) with 3 in HR. exact HR.
Qed.
Lemma p5_fin_run : forall (mdc : Model) (nF ovF : Z) (wr : list Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 16 = w64 n0 -> getr regs 12 = w64 ov0 -> getr regs 17 = w64 32 -> getr regs 11 = w64 1 ->
  getr regs 15 = w64 3 -> getr regs 13 = w64 47 -> getr regs 14 = w64 (VAL (A_OBJ 28)) ->
  getr regs 20 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  p5_nn n0 3 = nF -> p5_ovv n0 ov0 3 = ovF -> p5_wrl n0 3 = wr ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L5) regs memc mdc)
    (rbn_lpost B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L5X [5; 6; 10; 11; 12; 16; 17]
       D n0 wr [(16, nF); (12, ovF)]).
Proof.
intros mdc nF ovF wr HJ R16 R12 R17 R11 R15 R13 R14 R20 R22 HnF HovF HwF.
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
eapply SRr_mono.
{ apply (p5_all regs memc mdc HJ).
  unfold p5_pkg. split; [intros a Ha Hn; reflexivity|].
  split.
  { unfold p5_wrl, p5_cnt. rewrite Z.min_l by lia.
    intros j Hj. vm_compute in Hj. lia. }
  split; [intros a Ha; exact (proj2 (HBW a Ha))|].
  split; [intros r Hr Hnin; reflexivity|].
  split; [unfold p5_nn, p5_cnt; rewrite Z.min_l by lia; rewrite Z.add_0_r; exact R16|].
  split; [unfold p5_ovv; replace (n0 + 1 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; lia);
          exact R12|].
  split; [cbn [Z.to_nat rbn_lit5 nth]; exact R17|].
  split; [exact R11|]. split; [exact R15|]. split; [exact R13|]. split; [exact R14|].
  split; [exact R20 | exact R22]. }
intros W2 c2 Hle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2).
destruct HP2 as (HEQ & HWR & HPR & HKEEP & Q16 & Q12 & Q17 & Q11 & Q15 & Q13 & Q14 & Q20 & Q22).
unfold rbn_lpost. split; [reflexivity|]. exists regs2, mem2, md2.
split.
{ unfold cfg_at, w64. cbn [Z.leb Z.compare].
  replace (BASE + AF_reac_box_name + RBN_L5X) with (BASE + 15792)
    by (unfold AF_reac_box_name, RBN_L5X; lia).
  reflexivity. }
split; [exact HJ2|]. split; [exact HKEEP|].
split.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
  - replace (Z_to_bv 5 16) with (16%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Q16, HnF. reflexivity.
  - replace (Z_to_bv 5 12) with (12%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Q12, HovF. reflexivity. }
rewrite <- HwF. split; [exact HEQ | exact HWR].
Qed.
End S5.
Theorem rbn_L5_fits_holds : rbn_L5_fits B.
Proof.
unfold rbn_L5_fits, rbn_L5_run.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 Hfit
  HJ HSRC HAL HBUF HSEP HN0 HOV0 R16 R12 R17 R11 R15 R13 R14 R20 R22.
eapply p5_fin_run; try eassumption.
all: first
  [ solve [unfold p5_nn, p5_cnt; lia]
  | solve [unfold p5_ovv; replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; lia);
           reflexivity]
  | solve [unfold p5_wrl, p5_cnt; replace (Z.min (3 - 1) (47 - n0)) with 2 by lia; reflexivity] ].
Qed.
Theorem rbn_L5_ovf_holds : rbn_L5_ovf B.
Proof.
unfold rbn_L5_ovf, rbn_L5_run.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 Hovf
  HJ HSRC HAL HBUF HSEP HN0 HOV0 R16 R12 R17 R11 R15 R13 R14 R20 R22.
eapply p5_fin_run; try eassumption.
all: first
  [ solve [unfold p5_nn, p5_cnt; lia]
  | solve [unfold p5_ovv; replace (n0 + 3 - 1 <=? 47) with false by (symmetry; apply Z.leb_gt; lia);
           reflexivity]
  | solve [unfold p5_wrl, p5_cnt; f_equal; f_equal; lia] ].
Qed.
Definition p6_cnt (n0 i : Z) : Z := Z.min (i - 1) (47 - n0).
Definition p6_nn (n0 i : Z) : Z := n0 + p6_cnt n0 i.
Definition p6_ovv (n0 ov0 i : Z) : Z := if n0 + i - 1 <=? 47 then ov0 else 1.
Definition p6_wrl (n0 i : Z) : list Z := firstn (Z.to_nat (p6_cnt n0 i)) rbn_lit6.
Section S6.
Context (fq : YK11.FPState).
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (A1 D n0 ov0 : Z).
Hypothesis HSRC : rbn_lsrc W memc (VAL (A_OBJ 29)) (rbn_lit6 ++ [0]).
Hypothesis HAL : VAL (A_OBJ 29) mod 8 = 0.
Hypothesis HA1lo : alloc_ceiling <= A1 + 120.
Hypothesis HA1hi : A1 + 128 <= 2 ^ 47.
Hypothesis HA1lit : A1 + 128 <= VAL (A_OBJ 29) \/ VAL (A_OBJ 29) + 7 <= A1 + 120.
Hypothesis HBUF : rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc D 48.
Hypothesis HSEP : VAL (A_OBJ 29) + 7 <= D \/ D + 48 <= VAL (A_OBJ 29).
Hypothesis HA1D : A1 + 128 <= D \/ D + 48 <= A1 + 120.
Hypothesis HN0 : 0 <= n0 <= 47.
Hypothesis HOV0 : ov0 = 0 \/ ov0 = 1.
Definition p6_pkg (i : Z) (regsE : bvmap 5 word) (memE : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + Z.of_nat (length (p6_wrl n0 i))) ->
     aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a) /\
  garr8 SEGS (mrestrict (w_H W) memE) (D + n0) (p6_wrl n0 i) /\
  (forall a, D <= a < D + 48 -> apresent (w_H W) memE a) /\
  rbn_keep_regs regs regsE [5; 10; 12; 15; 16; 17; 23] /\
  getr regsE 15 = w64 (p6_nn n0 i) /\ getr regsE 12 = w64 (p6_ovv n0 ov0 i) /\
  getr regsE 16 = w64 (nth (Z.to_nat (i - 1)) rbn_lit6 0) /\
  getr regsE 23 = w64 i /\ getr regsE 14 = w64 7 /\ getr regsE 11 = w64 48 /\
  getr regsE 13 = w64 (VAL (A_OBJ 29)) /\ getr regsE 9 = w64 A1 /\
  val_mem SEGS (mrestrict (w_H W) memE) (A1 + 120) 8 D /\ getr regsE 22 = w64 SHADOW_OFF.
Definition p6_next (i : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = cfg_at (fx := fq) SEGS (BASE + (if i <=? 6 then 15852 else 15964)) regs2 mem2 md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ p6_pkg i regs2 mem2.
Definition p6_stmt (i : Z) : Prop :=
  forall (regsE : bvmap 5 word) memE mdE,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k ->
  p6_pkg i regsE memE ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L6) regsE memE mdE)
    (p6_next (i + 1)).
Lemma p6_it1 : p6_stmt 1.
Proof.
unfold p6_stmt, p6_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & Rn & Rov & Rc & Ri & Rlen & Rcap & Rlit & RA1 & RD & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 29%nat ltac:(unfold disco_nobj; lia)) as HOB. unfold IMG_LO, IMG_TOP in HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 29)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit6 ++ [0])) = 7) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p6_wrl n0 1)) = p6_cnt n0 1)
  by (unfold p6_wrl, p6_cnt; rewrite firstn_length; cbn [length rbn_lit6]; lia).
assert (Hc2 : 0 <= p6_cnt n0 1 <= 0) by (unfold p6_cnt; lia).
assert (HnB : p6_nn n0 1 = n0 + p6_cnt n0 1) by reflexivity.
assert (HnR : 0 <= p6_nn n0 1 <= 47) by (unfold p6_nn, p6_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p6_cnt n0 1) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 7).
{ apply (p_ra_eq (w_H W) memc memE lit 7); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit6 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit6 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
destruct (HRA2 (lit + 1) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 1) mod 8 = 1)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 1) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (1 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 1 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (Rc' : getr regsE 16 = w64 32) by (cbn in Rc; exact Rc).
pose proof (p6_entry fq W regsE memE 1 32 (p6_nn n0 1) (p6_ovv n0 ov0 1) A1 D sv
  Rn Rov Rc' Ri Rlen Rcap Rlit RA1 R22 RD HA1lo HA1hi HA1lit HA1D ltac:(lia) ltac:(lia) HnR HAPP HD63 HAL HSEP HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := E6 regsE (D + p6_nn n0 1) sv sa D) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E5; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D + p6_nn n0 1; sv; sa; D])) E)
  by (unfold E, E5; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + p6_nn n0 1; sv; sa; D])) m)
  by (intros m Hm; unfold E, E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (Edn : ew E 32 = Z_to_bv 64 (D + p6_nn n0 1))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (Esv : ew E 33 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U32 : U E (SOff 32 0) = D + p6_nn n0 1) by (apply (U_atom E 32 _ Edn); lia).
assert (U22 : U E P6BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P6BX P6SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P6SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U32, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U32, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L6)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P6SPAN.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
  ltac:(intros a (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K1.
rename HG into HG1. clear HF HFr.
assert (En : ew E 15 = Z_to_bv 64 (p6_nn n0 1)) by (rewrite (EE 15%nat 15%bv eq_refl); exact Rn).
assert (Bdn : bv_unsigned (ew E 32) = D + p6_nn n0 1) by (rewrite Edn; apply unsigned_lit_small; lia).
assert (Elit : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact Rlit).
assert (Blit : bv_unsigned (ew E 13) = lit) by (rewrite Elit; apply unsigned_lit_small; lia).
assert (Esa : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (Bsa : bv_unsigned (ew E 34) = sa) by (rewrite Esa; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact RA1).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK P6SPAN.
- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 1) 1 En) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hn47 : p6_nn n0 1 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 2 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 2 = p6_nn n0 1) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 2 = p6_wrl n0 1) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 2 = 1).
    { unfold p6_ovv. replace (n0 + 2 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (1 + 1) with 2. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 1)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 2 = p6_nn n0 1) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 2 = p6_wrl n0 1) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 2 = 1).
    { unfold p6_ovv. replace (n0 + 2 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (1 + 1) with 2. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 1)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 1) 1 En) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hn46 : p6_nn n0 1 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p6_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p6_nn n0 1) Bdn ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p6_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p6_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Bdn, Blit, Bsa, B9;
          repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  {     lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_gen E _ _ STK sp0 FP _ _ lyc own 32%nat (D + p6_nn n0 1));
      [reflexivity | exact Bdn | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBW a ltac:(lia)) |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p6_nn n0 1) (D + p6_nn n0 1 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?Bdn, ?Blit, ?Bsa, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 2 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p_awr_store Edn (D + p6_nn n0 1) HBW. }
    p_frame HFr (D + p6_nn n0 1) (D + p6_nn n0 1 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p6_nn n0 1) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p6_cnt n0 1 = 0) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 2 = 1) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 2)) = p6_cnt n0 2)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 2 = p6_nn n0 1 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 2 = p6_ovv n0 ov0 1).
    { unfold p6_ovv.
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 1 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 2 = p6_wrl n0 1 ++ [32]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (1 + 1) with 2. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 1)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 0) with (D + p6_nn n0 1) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p_awr_store Edn (D + p6_nn n0 1) HBW. }
    p_frame HFr (D + p6_nn n0 1) (D + p6_nn n0 1 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p6_nn n0 1) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p6_cnt n0 1 = 0) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 2 = 1) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 2)) = p6_cnt n0 2)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 2 = p6_nn n0 1 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 2 = p6_ovv n0 ov0 1).
    { unfold p6_ovv.
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 1 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 2 = p6_wrl n0 1 ++ [32]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (1 + 1) with 2. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 1)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 0) with (D + p6_nn n0 1) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

Qed.
Lemma p6_it2 : p6_stmt 2.
Proof.
unfold p6_stmt, p6_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & Rn & Rov & Rc & Ri & Rlen & Rcap & Rlit & RA1 & RD & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 29%nat ltac:(unfold disco_nobj; lia)) as HOB. unfold IMG_LO, IMG_TOP in HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 29)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit6 ++ [0])) = 7) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p6_wrl n0 2)) = p6_cnt n0 2)
  by (unfold p6_wrl, p6_cnt; rewrite firstn_length; cbn [length rbn_lit6]; lia).
assert (Hc2 : 0 <= p6_cnt n0 2 <= 1) by (unfold p6_cnt; lia).
assert (HnB : p6_nn n0 2 = n0 + p6_cnt n0 2) by reflexivity.
assert (HnR : 0 <= p6_nn n0 2 <= 47) by (unfold p6_nn, p6_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p6_cnt n0 2) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 7).
{ apply (p_ra_eq (w_H W) memc memE lit 7); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit6 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit6 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
destruct (HRA2 (lit + 2) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 2) mod 8 = 2)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 2) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (2 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 2 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (Rc' : getr regsE 16 = w64 105) by (cbn in Rc; exact Rc).
pose proof (p6_entry fq W regsE memE 2 105 (p6_nn n0 2) (p6_ovv n0 ov0 2) A1 D sv
  Rn Rov Rc' Ri Rlen Rcap Rlit RA1 R22 RD HA1lo HA1hi HA1lit HA1D ltac:(lia) ltac:(lia) HnR HAPP HD63 HAL HSEP HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := E6 regsE (D + p6_nn n0 2) sv sa D) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E5; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D + p6_nn n0 2; sv; sa; D])) E)
  by (unfold E, E5; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + p6_nn n0 2; sv; sa; D])) m)
  by (intros m Hm; unfold E, E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (Edn : ew E 32 = Z_to_bv 64 (D + p6_nn n0 2))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (Esv : ew E 33 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U32 : U E (SOff 32 0) = D + p6_nn n0 2) by (apply (U_atom E 32 _ Edn); lia).
assert (U22 : U E P6BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P6BX P6SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P6SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U32, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U32, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L6)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P6SPAN.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
  ltac:(intros a (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K1.
rename HG into HG1. clear HF HFr.
assert (En : ew E 15 = Z_to_bv 64 (p6_nn n0 2)) by (rewrite (EE 15%nat 15%bv eq_refl); exact Rn).
assert (Bdn : bv_unsigned (ew E 32) = D + p6_nn n0 2) by (rewrite Edn; apply unsigned_lit_small; lia).
assert (Elit : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact Rlit).
assert (Blit : bv_unsigned (ew E 13) = lit) by (rewrite Elit; apply unsigned_lit_small; lia).
assert (Esa : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (Bsa : bv_unsigned (ew E 34) = sa) by (rewrite Esa; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact RA1).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK P6SPAN.
- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 2) 1 En) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hn47 : p6_nn n0 2 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 3 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 3 = p6_nn n0 2) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 3 = p6_wrl n0 2) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 3 = 1).
    { unfold p6_ovv. replace (n0 + 3 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (2 + 1) with 3. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 2)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 3 = p6_nn n0 2) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 3 = p6_wrl n0 2) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 3 = 1).
    { unfold p6_ovv. replace (n0 + 3 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (2 + 1) with 3. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 2)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 2) 1 En) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hn46 : p6_nn n0 2 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p6_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p6_nn n0 2) Bdn ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p6_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p6_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Bdn, Blit, Bsa, B9;
          repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  {     lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_gen E _ _ STK sp0 FP _ _ lyc own 32%nat (D + p6_nn n0 2));
      [reflexivity | exact Bdn | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBW a ltac:(lia)) |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p6_nn n0 2) (D + p6_nn n0 2 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?Bdn, ?Blit, ?Bsa, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 3 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p_awr_store Edn (D + p6_nn n0 2) HBW. }
    p_frame HFr (D + p6_nn n0 2) (D + p6_nn n0 2 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p6_nn n0 2) _ 0 1 0 1 0 1%N (SLit 105) 105 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p6_cnt n0 2 = 1) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 3 = 2) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 3)) = p6_cnt n0 3)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 3 = p6_nn n0 2 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 3 = p6_ovv n0 ov0 2).
    { unfold p6_ovv.
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 3 = p6_wrl n0 2 ++ [105]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (2 + 1) with 3. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 2)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 1) with (D + p6_nn n0 2) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p_awr_store Edn (D + p6_nn n0 2) HBW. }
    p_frame HFr (D + p6_nn n0 2) (D + p6_nn n0 2 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p6_nn n0 2) _ 0 1 0 1 0 1%N (SLit 105) 105 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p6_cnt n0 2 = 1) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 3 = 2) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 3)) = p6_cnt n0 3)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 3 = p6_nn n0 2 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 3 = p6_ovv n0 ov0 2).
    { unfold p6_ovv.
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 3 = p6_wrl n0 2 ++ [105]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (2 + 1) with 3. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 2)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 1) with (D + p6_nn n0 2) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

Qed.
Lemma p6_it3 : p6_stmt 3.
Proof.
unfold p6_stmt, p6_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & Rn & Rov & Rc & Ri & Rlen & Rcap & Rlit & RA1 & RD & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 29%nat ltac:(unfold disco_nobj; lia)) as HOB. unfold IMG_LO, IMG_TOP in HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 29)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit6 ++ [0])) = 7) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p6_wrl n0 3)) = p6_cnt n0 3)
  by (unfold p6_wrl, p6_cnt; rewrite firstn_length; cbn [length rbn_lit6]; lia).
assert (Hc2 : 0 <= p6_cnt n0 3 <= 2) by (unfold p6_cnt; lia).
assert (HnB : p6_nn n0 3 = n0 + p6_cnt n0 3) by reflexivity.
assert (HnR : 0 <= p6_nn n0 3 <= 47) by (unfold p6_nn, p6_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p6_cnt n0 3) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 7).
{ apply (p_ra_eq (w_H W) memc memE lit 7); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit6 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit6 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
destruct (HRA2 (lit + 3) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 3) mod 8 = 3)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 3) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (3 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 3 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (Rc' : getr regsE 16 = w64 110) by (cbn in Rc; exact Rc).
pose proof (p6_entry fq W regsE memE 3 110 (p6_nn n0 3) (p6_ovv n0 ov0 3) A1 D sv
  Rn Rov Rc' Ri Rlen Rcap Rlit RA1 R22 RD HA1lo HA1hi HA1lit HA1D ltac:(lia) ltac:(lia) HnR HAPP HD63 HAL HSEP HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := E6 regsE (D + p6_nn n0 3) sv sa D) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E5; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D + p6_nn n0 3; sv; sa; D])) E)
  by (unfold E, E5; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + p6_nn n0 3; sv; sa; D])) m)
  by (intros m Hm; unfold E, E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (Edn : ew E 32 = Z_to_bv 64 (D + p6_nn n0 3))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (Esv : ew E 33 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U32 : U E (SOff 32 0) = D + p6_nn n0 3) by (apply (U_atom E 32 _ Edn); lia).
assert (U22 : U E P6BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P6BX P6SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P6SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U32, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U32, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L6)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P6SPAN.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
  ltac:(intros a (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K1.
rename HG into HG1. clear HF HFr.
assert (En : ew E 15 = Z_to_bv 64 (p6_nn n0 3)) by (rewrite (EE 15%nat 15%bv eq_refl); exact Rn).
assert (Bdn : bv_unsigned (ew E 32) = D + p6_nn n0 3) by (rewrite Edn; apply unsigned_lit_small; lia).
assert (Elit : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact Rlit).
assert (Blit : bv_unsigned (ew E 13) = lit) by (rewrite Elit; apply unsigned_lit_small; lia).
assert (Esa : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (Bsa : bv_unsigned (ew E 34) = sa) by (rewrite Esa; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact RA1).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK P6SPAN.
- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 3) 1 En) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hn47 : p6_nn n0 3 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 4 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 4 = p6_nn n0 3) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 4 = p6_wrl n0 3) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 4 = 1).
    { unfold p6_ovv. replace (n0 + 4 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (3 + 1) with 4. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 3)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 4 = p6_nn n0 3) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 4 = p6_wrl n0 3) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 4 = 1).
    { unfold p6_ovv. replace (n0 + 4 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (3 + 1) with 4. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 3)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 3) 1 En) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hn46 : p6_nn n0 3 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p6_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p6_nn n0 3) Bdn ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p6_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p6_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Bdn, Blit, Bsa, B9;
          repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  {     lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_gen E _ _ STK sp0 FP _ _ lyc own 32%nat (D + p6_nn n0 3));
      [reflexivity | exact Bdn | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBW a ltac:(lia)) |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p6_nn n0 3) (D + p6_nn n0 3 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?Bdn, ?Blit, ?Bsa, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 4 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p_awr_store Edn (D + p6_nn n0 3) HBW. }
    p_frame HFr (D + p6_nn n0 3) (D + p6_nn n0 3 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p6_nn n0 3) _ 0 1 0 1 0 1%N (SLit 110) 110 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p6_cnt n0 3 = 2) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 4 = 3) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 4)) = p6_cnt n0 4)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 4 = p6_nn n0 3 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 4 = p6_ovv n0 ov0 3).
    { unfold p6_ovv.
      replace (n0 + 4 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 4 = p6_wrl n0 3 ++ [110]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (3 + 1) with 4. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 3)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 2) with (D + p6_nn n0 3) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p_awr_store Edn (D + p6_nn n0 3) HBW. }
    p_frame HFr (D + p6_nn n0 3) (D + p6_nn n0 3 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p6_nn n0 3) _ 0 1 0 1 0 1%N (SLit 110) 110 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p6_cnt n0 3 = 2) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 4 = 3) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 4)) = p6_cnt n0 4)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 4 = p6_nn n0 3 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 4 = p6_ovv n0 ov0 3).
    { unfold p6_ovv.
      replace (n0 + 4 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 4 = p6_wrl n0 3 ++ [110]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (3 + 1) with 4. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 3)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 2) with (D + p6_nn n0 3) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

Qed.
Lemma p6_it4 : p6_stmt 4.
Proof.
unfold p6_stmt, p6_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & Rn & Rov & Rc & Ri & Rlen & Rcap & Rlit & RA1 & RD & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 29%nat ltac:(unfold disco_nobj; lia)) as HOB. unfold IMG_LO, IMG_TOP in HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 29)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit6 ++ [0])) = 7) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p6_wrl n0 4)) = p6_cnt n0 4)
  by (unfold p6_wrl, p6_cnt; rewrite firstn_length; cbn [length rbn_lit6]; lia).
assert (Hc2 : 0 <= p6_cnt n0 4 <= 3) by (unfold p6_cnt; lia).
assert (HnB : p6_nn n0 4 = n0 + p6_cnt n0 4) by reflexivity.
assert (HnR : 0 <= p6_nn n0 4 <= 47) by (unfold p6_nn, p6_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p6_cnt n0 4) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 7).
{ apply (p_ra_eq (w_H W) memc memE lit 7); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit6 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit6 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
destruct (HRA2 (lit + 4) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 4) mod 8 = 4)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 4) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (4 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 4 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (Rc' : getr regsE 16 = w64 32) by (cbn in Rc; exact Rc).
pose proof (p6_entry fq W regsE memE 4 32 (p6_nn n0 4) (p6_ovv n0 ov0 4) A1 D sv
  Rn Rov Rc' Ri Rlen Rcap Rlit RA1 R22 RD HA1lo HA1hi HA1lit HA1D ltac:(lia) ltac:(lia) HnR HAPP HD63 HAL HSEP HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := E6 regsE (D + p6_nn n0 4) sv sa D) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E5; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D + p6_nn n0 4; sv; sa; D])) E)
  by (unfold E, E5; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + p6_nn n0 4; sv; sa; D])) m)
  by (intros m Hm; unfold E, E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (Edn : ew E 32 = Z_to_bv 64 (D + p6_nn n0 4))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (Esv : ew E 33 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U32 : U E (SOff 32 0) = D + p6_nn n0 4) by (apply (U_atom E 32 _ Edn); lia).
assert (U22 : U E P6BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P6BX P6SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P6SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U32, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U32, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L6)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P6SPAN.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
  ltac:(intros a (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K1.
rename HG into HG1. clear HF HFr.
assert (En : ew E 15 = Z_to_bv 64 (p6_nn n0 4)) by (rewrite (EE 15%nat 15%bv eq_refl); exact Rn).
assert (Bdn : bv_unsigned (ew E 32) = D + p6_nn n0 4) by (rewrite Edn; apply unsigned_lit_small; lia).
assert (Elit : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact Rlit).
assert (Blit : bv_unsigned (ew E 13) = lit) by (rewrite Elit; apply unsigned_lit_small; lia).
assert (Esa : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (Bsa : bv_unsigned (ew E 34) = sa) by (rewrite Esa; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact RA1).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK P6SPAN.
- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 4) 1 En) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hn47 : p6_nn n0 4 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 5 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 5 = p6_nn n0 4) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 5 = p6_wrl n0 4) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 5 = 1).
    { unfold p6_ovv. replace (n0 + 5 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (4 + 1) with 5. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 4)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 5 = p6_nn n0 4) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 5 = p6_wrl n0 4) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 5 = 1).
    { unfold p6_ovv. replace (n0 + 5 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (4 + 1) with 5. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 4)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 4) 1 En) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hn46 : p6_nn n0 4 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p6_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p6_nn n0 4) Bdn ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p6_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p6_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Bdn, Blit, Bsa, B9;
          repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  {     lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_gen E _ _ STK sp0 FP _ _ lyc own 32%nat (D + p6_nn n0 4));
      [reflexivity | exact Bdn | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBW a ltac:(lia)) |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p6_nn n0 4) (D + p6_nn n0 4 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?Bdn, ?Blit, ?Bsa, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 5 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p_awr_store Edn (D + p6_nn n0 4) HBW. }
    p_frame HFr (D + p6_nn n0 4) (D + p6_nn n0 4 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p6_nn n0 4) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p6_cnt n0 4 = 3) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 5 = 4) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 5)) = p6_cnt n0 5)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 5 = p6_nn n0 4 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 5 = p6_ovv n0 ov0 4).
    { unfold p6_ovv.
      replace (n0 + 5 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 4 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 5 = p6_wrl n0 4 ++ [32]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (4 + 1) with 5. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 4)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 3) with (D + p6_nn n0 4) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p_awr_store Edn (D + p6_nn n0 4) HBW. }
    p_frame HFr (D + p6_nn n0 4) (D + p6_nn n0 4 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p6_nn n0 4) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p6_cnt n0 4 = 3) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 5 = 4) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 5)) = p6_cnt n0 5)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 5 = p6_nn n0 4 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 5 = p6_ovv n0 ov0 4).
    { unfold p6_ovv.
      replace (n0 + 5 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 4 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 5 = p6_wrl n0 4 ++ [32]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (4 + 1) with 5. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 4)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 3) with (D + p6_nn n0 4) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

Qed.
Lemma p6_it5 : p6_stmt 5.
Proof.
unfold p6_stmt, p6_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & Rn & Rov & Rc & Ri & Rlen & Rcap & Rlit & RA1 & RD & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 29%nat ltac:(unfold disco_nobj; lia)) as HOB. unfold IMG_LO, IMG_TOP in HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 29)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit6 ++ [0])) = 7) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p6_wrl n0 5)) = p6_cnt n0 5)
  by (unfold p6_wrl, p6_cnt; rewrite firstn_length; cbn [length rbn_lit6]; lia).
assert (Hc2 : 0 <= p6_cnt n0 5 <= 4) by (unfold p6_cnt; lia).
assert (HnB : p6_nn n0 5 = n0 + p6_cnt n0 5) by reflexivity.
assert (HnR : 0 <= p6_nn n0 5 <= 47) by (unfold p6_nn, p6_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p6_cnt n0 5) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 7).
{ apply (p_ra_eq (w_H W) memc memE lit 7); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit6 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit6 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
destruct (HRA2 (lit + 5) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 5) mod 8 = 5)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 5) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (5 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 5 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (Rc' : getr regsE 16 = w64 47) by (cbn in Rc; exact Rc).
pose proof (p6_entry fq W regsE memE 5 47 (p6_nn n0 5) (p6_ovv n0 ov0 5) A1 D sv
  Rn Rov Rc' Ri Rlen Rcap Rlit RA1 R22 RD HA1lo HA1hi HA1lit HA1D ltac:(lia) ltac:(lia) HnR HAPP HD63 HAL HSEP HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := E6 regsE (D + p6_nn n0 5) sv sa D) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E5; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D + p6_nn n0 5; sv; sa; D])) E)
  by (unfold E, E5; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + p6_nn n0 5; sv; sa; D])) m)
  by (intros m Hm; unfold E, E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (Edn : ew E 32 = Z_to_bv 64 (D + p6_nn n0 5))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (Esv : ew E 33 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U32 : U E (SOff 32 0) = D + p6_nn n0 5) by (apply (U_atom E 32 _ Edn); lia).
assert (U22 : U E P6BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P6BX P6SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P6SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U32, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U32, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L6)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P6SPAN.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
  ltac:(intros a (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K1.
rename HG into HG1. clear HF HFr.
assert (En : ew E 15 = Z_to_bv 64 (p6_nn n0 5)) by (rewrite (EE 15%nat 15%bv eq_refl); exact Rn).
assert (Bdn : bv_unsigned (ew E 32) = D + p6_nn n0 5) by (rewrite Edn; apply unsigned_lit_small; lia).
assert (Elit : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact Rlit).
assert (Blit : bv_unsigned (ew E 13) = lit) by (rewrite Elit; apply unsigned_lit_small; lia).
assert (Esa : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (Bsa : bv_unsigned (ew E 34) = sa) by (rewrite Esa; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact RA1).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK P6SPAN.
- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 5) 1 En) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hn47 : p6_nn n0 5 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 6 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 6 = p6_nn n0 5) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 6 = p6_wrl n0 5) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 6 = 1).
    { unfold p6_ovv. replace (n0 + 6 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (5 + 1) with 6. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 5)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 6 = p6_nn n0 5) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 6 = p6_wrl n0 5) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 6 = 1).
    { unfold p6_ovv. replace (n0 + 6 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (5 + 1) with 6. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 5)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 5) 1 En) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hn46 : p6_nn n0 5 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p6_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p6_nn n0 5) Bdn ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p6_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p6_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Bdn, Blit, Bsa, B9;
          repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  {     lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_gen E _ _ STK sp0 FP _ _ lyc own 32%nat (D + p6_nn n0 5));
      [reflexivity | exact Bdn | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBW a ltac:(lia)) |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p6_nn n0 5) (D + p6_nn n0 5 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?Bdn, ?Blit, ?Bsa, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 6 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p_awr_store Edn (D + p6_nn n0 5) HBW. }
    p_frame HFr (D + p6_nn n0 5) (D + p6_nn n0 5 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p6_nn n0 5) _ 0 1 0 1 0 1%N (SLit 47) 47 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p6_cnt n0 5 = 4) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 6 = 5) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 6)) = p6_cnt n0 6)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 6 = p6_nn n0 5 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 6 = p6_ovv n0 ov0 5).
    { unfold p6_ovv.
      replace (n0 + 6 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 5 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 6 = p6_wrl n0 5 ++ [47]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (5 + 1) with 6. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 5)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 4) with (D + p6_nn n0 5) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p_awr_store Edn (D + p6_nn n0 5) HBW. }
    p_frame HFr (D + p6_nn n0 5) (D + p6_nn n0 5 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p6_nn n0 5) _ 0 1 0 1 0 1%N (SLit 47) 47 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p6_cnt n0 5 = 4) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 6 = 5) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 6)) = p6_cnt n0 6)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 6 = p6_nn n0 5 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 6 = p6_ovv n0 ov0 5).
    { unfold p6_ovv.
      replace (n0 + 6 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 5 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 6 = p6_wrl n0 5 ++ [47]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (5 + 1) with 6. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 5)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 4) with (D + p6_nn n0 5) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

Qed.
Lemma p6_it6 : p6_stmt 6.
Proof.
unfold p6_stmt, p6_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & Rn & Rov & Rc & Ri & Rlen & Rcap & Rlit & RA1 & RD & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 29%nat ltac:(unfold disco_nobj; lia)) as HOB. unfold IMG_LO, IMG_TOP in HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 29)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit6 ++ [0])) = 7) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p6_wrl n0 6)) = p6_cnt n0 6)
  by (unfold p6_wrl, p6_cnt; rewrite firstn_length; cbn [length rbn_lit6]; lia).
assert (Hc2 : 0 <= p6_cnt n0 6 <= 5) by (unfold p6_cnt; lia).
assert (HnB : p6_nn n0 6 = n0 + p6_cnt n0 6) by reflexivity.
assert (HnR : 0 <= p6_nn n0 6 <= 47) by (unfold p6_nn, p6_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p6_cnt n0 6) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 7).
{ apply (p_ra_eq (w_H W) memc memE lit 7); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit6 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit6 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
destruct (HRA2 (lit + 6) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 6) mod 8 = 6)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 6) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (6 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 6 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (Rc' : getr regsE 16 = w64 32) by (cbn in Rc; exact Rc).
pose proof (p6_entry fq W regsE memE 6 32 (p6_nn n0 6) (p6_ovv n0 ov0 6) A1 D sv
  Rn Rov Rc' Ri Rlen Rcap Rlit RA1 R22 RD HA1lo HA1hi HA1lit HA1D ltac:(lia) ltac:(lia) HnR HAPP HD63 HAL HSEP HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := E6 regsE (D + p6_nn n0 6) sv sa D) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E5; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D + p6_nn n0 6; sv; sa; D])) E)
  by (unfold E, E5; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + p6_nn n0 6; sv; sa; D])) m)
  by (intros m Hm; unfold E, E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (Edn : ew E 32 = Z_to_bv 64 (D + p6_nn n0 6))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (Esv : ew E 33 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U32 : U E (SOff 32 0) = D + p6_nn n0 6) by (apply (U_atom E 32 _ Edn); lia).
assert (U22 : U E P6BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P6BX P6SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P6SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U32, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U32, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L6)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P6SPAN.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
  ltac:(intros a (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K1.
rename HG into HG1. clear HF HFr.
assert (En : ew E 15 = Z_to_bv 64 (p6_nn n0 6)) by (rewrite (EE 15%nat 15%bv eq_refl); exact Rn).
assert (Bdn : bv_unsigned (ew E 32) = D + p6_nn n0 6) by (rewrite Edn; apply unsigned_lit_small; lia).
assert (Elit : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact Rlit).
assert (Blit : bv_unsigned (ew E 13) = lit) by (rewrite Elit; apply unsigned_lit_small; lia).
assert (Esa : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (Bsa : bv_unsigned (ew E 34) = sa) by (rewrite Esa; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact RA1).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK P6SPAN.
- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 6) 1 En) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hn47 : p6_nn n0 6 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 7 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6X).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 7 = p6_nn n0 6) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 7 = p6_wrl n0 6) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 7 = 1).
    { unfold p6_ovv. replace (n0 + 7 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (6 + 1) with 7. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 6)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6X).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 7 = p6_nn n0 6) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 7 = p6_wrl n0 6) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 7 = 1).
    { unfold p6_ovv. replace (n0 + 7 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (6 + 1) with 7. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 6)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 6) 1 En) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hn46 : p6_nn n0 6 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p6_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p6_nn n0 6) Bdn ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p6_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p6_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Bdn, Blit, Bsa, B9;
          repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  {     lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_gen E _ _ STK sp0 FP _ _ lyc own 32%nat (D + p6_nn n0 6));
      [reflexivity | exact Bdn | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBW a ltac:(lia)) |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p6_nn n0 6) (D + p6_nn n0 6 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?Bdn, ?Blit, ?Bsa, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 7 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6X).
    { p_awr_store Edn (D + p6_nn n0 6) HBW. }
    p_frame HFr (D + p6_nn n0 6) (D + p6_nn n0 6 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p6_nn n0 6) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p6_cnt n0 6 = 5) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 7 = 6) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 7)) = p6_cnt n0 7)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 7 = p6_nn n0 6 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 7 = p6_ovv n0 ov0 6).
    { unfold p6_ovv.
      replace (n0 + 7 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 6 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 7 = p6_wrl n0 6 ++ [32]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (6 + 1) with 7. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 6)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 5) with (D + p6_nn n0 6) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6X).
    { p_awr_store Edn (D + p6_nn n0 6) HBW. }
    p_frame HFr (D + p6_nn n0 6) (D + p6_nn n0 6 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p6_nn n0 6) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (16%bv : bv 5) Qc.
    prreg HS (23%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p6_cnt n0 6 = 5) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 7 = 6) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 7)) = p6_cnt n0 7)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 7 = p6_nn n0 6 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 7 = p6_ovv n0 ov0 6).
    { unfold p6_ovv.
      replace (n0 + 7 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 6 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 7 = p6_wrl n0 6 ++ [32]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (6 + 1) with 7. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 6)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 5) with (D + p6_nn n0 6) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

Qed.
Lemma p6_all : forall (regsE : bvmap 5 word) memE mdE,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k ->
  p6_pkg 1 regsE memE ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L6) regsE memE mdE)
    (p6_next 7).
Proof.
intros regsE memE mdE HJ HP.
eapply SRr_bind; [exact (p6_it1 regsE memE mdE HJ HP)|].
intros W2 c2 Hle2 Hx2. change (1 + 1) with 2 in Hx2.
destruct Hx2 as (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2).
assert (Hpc2 : (if (2 : Z) <=? 6 then 15852 else 15964) = AF_reac_box_name + RBN_L6)
  by reflexivity.
rewrite Hpc2.
replace (BASE + (AF_reac_box_name + RBN_L6)) with (BASE + AF_reac_box_name + RBN_L6) by lia.
eapply SRr_bind; [exact (p6_it2 regs2 mem2 md2 HJ2 HP2)|].
intros W3 c3 Hle3 Hx3. change (2 + 1) with 3 in Hx3.
destruct Hx3 as (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3).
assert (Hpc3 : (if (3 : Z) <=? 6 then 15852 else 15964) = AF_reac_box_name + RBN_L6)
  by reflexivity.
rewrite Hpc3.
replace (BASE + (AF_reac_box_name + RBN_L6)) with (BASE + AF_reac_box_name + RBN_L6) by lia.
eapply SRr_bind; [exact (p6_it3 regs3 mem3 md3 HJ3 HP3)|].
intros W4 c4 Hle4 Hx4. change (3 + 1) with 4 in Hx4.
destruct Hx4 as (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4).
assert (Hpc4 : (if (4 : Z) <=? 6 then 15852 else 15964) = AF_reac_box_name + RBN_L6)
  by reflexivity.
rewrite Hpc4.
replace (BASE + (AF_reac_box_name + RBN_L6)) with (BASE + AF_reac_box_name + RBN_L6) by lia.
eapply SRr_bind; [exact (p6_it4 regs4 mem4 md4 HJ4 HP4)|].
intros W5 c5 Hle5 Hx5. change (4 + 1) with 5 in Hx5.
destruct Hx5 as (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5).
assert (Hpc5 : (if (5 : Z) <=? 6 then 15852 else 15964) = AF_reac_box_name + RBN_L6)
  by reflexivity.
rewrite Hpc5.
replace (BASE + (AF_reac_box_name + RBN_L6)) with (BASE + AF_reac_box_name + RBN_L6) by lia.
eapply SRr_bind; [exact (p6_it5 regs5 mem5 md5 HJ5 HP5)|].
intros W6 c6 Hle6 Hx6. change (5 + 1) with 6 in Hx6.
destruct Hx6 as (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6).
assert (Hpc6 : (if (6 : Z) <=? 6 then 15852 else 15964) = AF_reac_box_name + RBN_L6)
  by reflexivity.
rewrite Hpc6.
replace (BASE + (AF_reac_box_name + RBN_L6)) with (BASE + AF_reac_box_name + RBN_L6) by lia.
pose proof (p6_it6 regs6 mem6 md6 HJ6 HP6) as HR.
change (6 + 1) with 7 in HR. exact HR.
Qed.
Lemma p6_fin_run : forall (mdc : Model) (nF ovF : Z) (wr : list Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 15 = w64 n0 -> getr regs 12 = w64 ov0 -> getr regs 16 = w64 32 ->
  getr regs 23 = w64 1 -> getr regs 14 = w64 7 -> getr regs 11 = w64 48 ->
  getr regs 13 = w64 (VAL (A_OBJ 29)) -> getr regs 9 = w64 A1 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A1 + 120) 8 D -> getr regs 22 = w64 SHADOW_OFF ->
  p6_nn n0 7 = nF -> p6_ovv n0 ov0 7 = ovF -> p6_wrl n0 7 = wr ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L6) regs memc mdc)
    (rbn_lpost B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L6X [5; 10; 12; 15; 16; 17; 23]
       D n0 wr [(15, nF); (12, ovF)]).
Proof.
intros mdc nF ovF wr HJ Rn Rov Rc Ri Rlen Rcap Rlit RA1 RD RSB HnF HovF HwF.
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
eapply SRr_mono.
{ apply (p6_all regs memc mdc HJ).
  unfold p6_pkg. split; [intros a Ha Hn; reflexivity|].
  split.
  { unfold p6_wrl, p6_cnt. rewrite Z.min_l by lia.
    intros j Hj. vm_compute in Hj. lia. }
  split; [intros a Ha; exact (proj2 (HBW a Ha))|].
  split; [intros r Hr Hnin; reflexivity|].
  split; [unfold p6_nn, p6_cnt; rewrite Z.min_l by lia; rewrite Z.add_0_r; exact Rn|].
  split; [unfold p6_ovv; replace (n0 + 1 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; lia);
          exact Rov|].
  split; [cbn [Z.to_nat rbn_lit6 nth]; exact Rc|].
  split; [exact Ri|]. split; [exact Rlen|]. split; [exact Rcap|]. split; [exact Rlit|].
  split; [exact RA1|]. split; [exact RD | exact RSB]. }
intros W2 c2 Hle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2).
destruct HP2 as (HEQ & HWR & HPR & HKEEP & Qn & Qov & Qc & Qi & Qlen & Qcap & Qlit & QA1 & QD & QSB).
unfold rbn_lpost. split; [reflexivity|]. exists regs2, mem2, md2.
split.
{ unfold cfg_at, w64. cbn [Z.leb Z.compare].
  replace (BASE + AF_reac_box_name + RBN_L6X) with (BASE + 15964)
    by (unfold AF_reac_box_name, RBN_L6X; lia).
  reflexivity. }
split; [exact HJ2|]. split; [exact HKEEP|].
split.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
  - replace (Z_to_bv 5 15) with (15%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Qn, HnF. reflexivity.
  - replace (Z_to_bv 5 12) with (12%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Qov, HovF. reflexivity. }
rewrite <- HwF. split; [exact HEQ | exact HWR].
Qed.
End S6.
Theorem rbn_L6_fits_holds : rbn_L6_fits B.
Proof.
unfold rbn_L6_fits, rbn_L6_run.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 Hfit
  HJ HSRC HAL HA1lo HA1hi HA1lit HBUF HSEP RD HA1D HN0 HOV0 Rn Rov Rc Ri Rlen Rcap Rlit RA1 RSB.
eapply p6_fin_run; try eassumption.
all: first
  [ solve [unfold p6_nn, p6_cnt; lia]
  | solve [unfold p6_ovv; replace (n0 + 7 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; lia);
           reflexivity]
  | solve [unfold p6_wrl, p6_cnt; replace (Z.min (7 - 1) (47 - n0)) with 6 by lia;
           reflexivity] ].
Qed.
Theorem rbn_L6_ovf_holds : rbn_L6_ovf B.
Proof.
unfold rbn_L6_ovf, rbn_L6_run.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 Hovf
  HJ HSRC HAL HA1lo HA1hi HA1lit HBUF HSEP RD HA1D HN0 HOV0 Rn Rov Rc Ri Rlen Rcap Rlit RA1 RSB.
eapply p6_fin_run; try eassumption.
all: first
  [ solve [unfold p6_nn, p6_cnt; lia]
  | solve [unfold p6_ovv; replace (n0 + 7 - 1 <=? 47) with false by (symmetry; apply Z.leb_gt; lia);
           reflexivity]
  | solve [unfold p6_wrl, p6_cnt; f_equal; f_equal; lia] ].
Qed.
Definition p7_cnt (n0 i : Z) : Z := Z.min (i - 1) (47 - n0).
Definition p7_nn (n0 i : Z) : Z := n0 + p7_cnt n0 i.
Definition p7_ovv (n0 ov0 i : Z) : Z := if n0 + i - 1 <=? 47 then ov0 else 1.
Definition p7_wrl (n0 i : Z) : list Z := firstn (Z.to_nat (p7_cnt n0 i)) rbn_lit7.
Section S7.
Context (fq : YK11.FPState).
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (A1 D n0 ov0 : Z).
Hypothesis HSRC : rbn_lsrc W memc (VAL (A_OBJ 30)) (rbn_lit7 ++ [0]).
Hypothesis HAL : VAL (A_OBJ 30) mod 8 = 0.
Hypothesis HA1lo : alloc_ceiling <= A1 + 120.
Hypothesis HA1hi : A1 + 128 <= 2 ^ 47.
Hypothesis HA1lit : A1 + 128 <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 6 <= A1 + 120.
Hypothesis HBUF : rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc D 48.
Hypothesis HSEP : VAL (A_OBJ 30) + 6 <= D \/ D + 48 <= VAL (A_OBJ 30).
Hypothesis HA1D : A1 + 128 <= D \/ D + 48 <= A1 + 120.
Hypothesis HN0 : 0 <= n0 <= 47.
Hypothesis HOV0 : ov0 = 0 \/ ov0 = 1.
Definition p7_pkg (i : Z) (regsE : bvmap 5 word) (memE : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + Z.of_nat (length (p7_wrl n0 i))) ->
     aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a) /\
  garr8 SEGS (mrestrict (w_H W) memE) (D + n0) (p7_wrl n0 i) /\
  (forall a, D <= a < D + 48 -> apresent (w_H W) memE a) /\
  rbn_keep_regs regs regsE [5; 10; 12; 15; 16; 17; 21; 23] /\
  getr regsE 23 = w64 (p7_nn n0 i) /\ getr regsE 12 = w64 (p7_ovv n0 ov0 i) /\
  getr regsE 15 = w64 (nth (Z.to_nat (i - 1)) rbn_lit7 0) /\
  getr regsE 21 = w64 i /\ getr regsE 14 = w64 6 /\ getr regsE 11 = w64 48 /\
  getr regsE 13 = w64 (VAL (A_OBJ 30)) /\ getr regsE 9 = w64 A1 /\
  val_mem SEGS (mrestrict (w_H W) memE) (A1 + 120) 8 D /\ getr regsE 22 = w64 SHADOW_OFF.
Definition p7_next (i : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = cfg_at (fx := fq) SEGS (BASE + (if i <=? 5 then 16020 else 16132)) regs2 mem2 md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ p7_pkg i regs2 mem2.
Definition p7_stmt (i : Z) : Prop :=
  forall (regsE : bvmap 5 word) memE mdE,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k ->
  p7_pkg i regsE memE ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L7) regsE memE mdE)
    (p7_next (i + 1)).
Lemma p7_it1 : p7_stmt 1.
Proof.
unfold p7_stmt, p7_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & Rn & Rov & Rc & Ri & Rlen & Rcap & Rlit & RA1 & RD & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 30%nat ltac:(unfold disco_nobj; lia)) as HOB. unfold IMG_LO, IMG_TOP in HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 30)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit7 ++ [0])) = 6) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p7_wrl n0 1)) = p7_cnt n0 1)
  by (unfold p7_wrl, p7_cnt; rewrite firstn_length; cbn [length rbn_lit7]; lia).
assert (Hc2 : 0 <= p7_cnt n0 1 <= 0) by (unfold p7_cnt; lia).
assert (HnB : p7_nn n0 1 = n0 + p7_cnt n0 1) by reflexivity.
assert (HnR : 0 <= p7_nn n0 1 <= 47) by (unfold p7_nn, p7_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p7_cnt n0 1) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 6).
{ apply (p_ra_eq (w_H W) memc memE lit 6); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit7 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit7 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
destruct (HRA2 (lit + 1) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 1) mod 8 = 1)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 1) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (1 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 1 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (Rc' : getr regsE 15 = w64 32) by (cbn in Rc; exact Rc).
pose proof (p7_entry fq W regsE memE 1 32 (p7_nn n0 1) (p7_ovv n0 ov0 1) A1 D sv
  Rn Rov Rc' Ri Rlen Rcap Rlit RA1 R22 RD HA1lo HA1hi HA1lit HA1D ltac:(lia) ltac:(lia) HnR HAPP HD63 HAL HSEP HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := E7 regsE (D + p7_nn n0 1) sv sa D) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E5; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D + p7_nn n0 1; sv; sa; D])) E)
  by (unfold E, E5; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + p7_nn n0 1; sv; sa; D])) m)
  by (intros m Hm; unfold E, E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (Edn : ew E 32 = Z_to_bv 64 (D + p7_nn n0 1))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (Esv : ew E 33 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U32 : U E (SOff 32 0) = D + p7_nn n0 1) by (apply (U_atom E 32 _ Edn); lia).
assert (U22 : U E P7BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P7BX P7SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P7SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U32, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U32, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L7)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L7)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P7SPAN.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
  ltac:(intros a (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K1.
rename HG into HG1. clear HF HFr.
assert (En : ew E 23 = Z_to_bv 64 (p7_nn n0 1)) by (rewrite (EE 23%nat 23%bv eq_refl); exact Rn).
assert (Bdn : bv_unsigned (ew E 32) = D + p7_nn n0 1) by (rewrite Edn; apply unsigned_lit_small; lia).
assert (Elit : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact Rlit).
assert (Blit : bv_unsigned (ew E 13) = lit) by (rewrite Elit; apply unsigned_lit_small; lia).
assert (Esa : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (Bsa : bv_unsigned (ew E 34) = sa) by (rewrite Esa; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact RA1).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK P7SPAN.
- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 23 (p7_nn n0 1) 1 En) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hn47 : p7_nn n0 1 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P7SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P7SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 2 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p7_nn n0 2 = p7_nn n0 1) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hw3 : p7_wrl n0 2 = p7_wrl n0 1) by (unfold p7_wrl, p7_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p7_ovv n0 ov0 2 = 1).
    { unfold p7_ovv. replace (n0 + 2 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p7_nn, p7_cnt in Hn47; lia]. }
    change (1 + 1) with 2. unfold p7_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 1)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p7_nn n0 2 = p7_nn n0 1) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hw3 : p7_wrl n0 2 = p7_wrl n0 1) by (unfold p7_wrl, p7_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p7_ovv n0 ov0 2 = 1).
    { unfold p7_ovv. replace (n0 + 2 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p7_nn, p7_cnt in Hn47; lia]. }
    change (1 + 1) with 2. unfold p7_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 1)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 23 (p7_nn n0 1) 1 En) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hn46 : p7_nn n0 1 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p7_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p7_nn n0 1) Bdn ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p7_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p7_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Bdn, Blit, Bsa, B9;
          repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P7SPAN.
  {     lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_gen E _ _ STK sp0 FP _ _ lyc own 32%nat (D + p7_nn n0 1));
      [reflexivity | exact Bdn | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBW a ltac:(lia)) |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p7_nn n0 1) (D + p7_nn n0 1 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?Bdn, ?Blit, ?Bsa, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P7SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 2 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { p_awr_store Edn (D + p7_nn n0 1) HBW. }
    p_frame HFr (D + p7_nn n0 1) (D + p7_nn n0 1 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p7_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p7_nn n0 1) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p7_cnt n0 1 = 0) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hc3e : p7_cnt n0 2 = 1) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p7_wrl n0 2)) = p7_cnt n0 2)
      by (unfold p7_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit7]; lia).
    assert (Hn3 : p7_nn n0 2 = p7_nn n0 1 + 1) by (unfold p7_nn; lia).
    assert (Ho3 : p7_ovv n0 ov0 2 = p7_ovv n0 ov0 1).
    { unfold p7_ovv.
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      replace (n0 + 1 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p7_wrl n0 2 = p7_wrl n0 1 ++ [32]).
    { unfold p7_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (1 + 1) with 2. unfold p7_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p7_nn, p7_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 1)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 0) with (D + p7_nn n0 1) by (unfold p7_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { p_awr_store Edn (D + p7_nn n0 1) HBW. }
    p_frame HFr (D + p7_nn n0 1) (D + p7_nn n0 1 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p7_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p7_nn n0 1) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p7_cnt n0 1 = 0) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hc3e : p7_cnt n0 2 = 1) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p7_wrl n0 2)) = p7_cnt n0 2)
      by (unfold p7_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit7]; lia).
    assert (Hn3 : p7_nn n0 2 = p7_nn n0 1 + 1) by (unfold p7_nn; lia).
    assert (Ho3 : p7_ovv n0 ov0 2 = p7_ovv n0 ov0 1).
    { unfold p7_ovv.
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      replace (n0 + 1 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p7_wrl n0 2 = p7_wrl n0 1 ++ [32]).
    { unfold p7_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (1 + 1) with 2. unfold p7_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p7_nn, p7_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 1)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 0) with (D + p7_nn n0 1) by (unfold p7_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

Qed.
Lemma p7_it2 : p7_stmt 2.
Proof.
unfold p7_stmt, p7_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & Rn & Rov & Rc & Ri & Rlen & Rcap & Rlit & RA1 & RD & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 30%nat ltac:(unfold disco_nobj; lia)) as HOB. unfold IMG_LO, IMG_TOP in HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 30)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit7 ++ [0])) = 6) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p7_wrl n0 2)) = p7_cnt n0 2)
  by (unfold p7_wrl, p7_cnt; rewrite firstn_length; cbn [length rbn_lit7]; lia).
assert (Hc2 : 0 <= p7_cnt n0 2 <= 1) by (unfold p7_cnt; lia).
assert (HnB : p7_nn n0 2 = n0 + p7_cnt n0 2) by reflexivity.
assert (HnR : 0 <= p7_nn n0 2 <= 47) by (unfold p7_nn, p7_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p7_cnt n0 2) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 6).
{ apply (p_ra_eq (w_H W) memc memE lit 6); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit7 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit7 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
destruct (HRA2 (lit + 2) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 2) mod 8 = 2)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 2) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (2 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 2 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (Rc' : getr regsE 15 = w64 111) by (cbn in Rc; exact Rc).
pose proof (p7_entry fq W regsE memE 2 111 (p7_nn n0 2) (p7_ovv n0 ov0 2) A1 D sv
  Rn Rov Rc' Ri Rlen Rcap Rlit RA1 R22 RD HA1lo HA1hi HA1lit HA1D ltac:(lia) ltac:(lia) HnR HAPP HD63 HAL HSEP HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := E7 regsE (D + p7_nn n0 2) sv sa D) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E5; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D + p7_nn n0 2; sv; sa; D])) E)
  by (unfold E, E5; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + p7_nn n0 2; sv; sa; D])) m)
  by (intros m Hm; unfold E, E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (Edn : ew E 32 = Z_to_bv 64 (D + p7_nn n0 2))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (Esv : ew E 33 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U32 : U E (SOff 32 0) = D + p7_nn n0 2) by (apply (U_atom E 32 _ Edn); lia).
assert (U22 : U E P7BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P7BX P7SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P7SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U32, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U32, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L7)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L7)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P7SPAN.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
  ltac:(intros a (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K1.
rename HG into HG1. clear HF HFr.
assert (En : ew E 23 = Z_to_bv 64 (p7_nn n0 2)) by (rewrite (EE 23%nat 23%bv eq_refl); exact Rn).
assert (Bdn : bv_unsigned (ew E 32) = D + p7_nn n0 2) by (rewrite Edn; apply unsigned_lit_small; lia).
assert (Elit : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact Rlit).
assert (Blit : bv_unsigned (ew E 13) = lit) by (rewrite Elit; apply unsigned_lit_small; lia).
assert (Esa : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (Bsa : bv_unsigned (ew E 34) = sa) by (rewrite Esa; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact RA1).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK P7SPAN.
- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 23 (p7_nn n0 2) 1 En) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hn47 : p7_nn n0 2 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P7SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P7SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 3 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p7_nn n0 3 = p7_nn n0 2) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hw3 : p7_wrl n0 3 = p7_wrl n0 2) by (unfold p7_wrl, p7_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p7_ovv n0 ov0 3 = 1).
    { unfold p7_ovv. replace (n0 + 3 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p7_nn, p7_cnt in Hn47; lia]. }
    change (2 + 1) with 3. unfold p7_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 2)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p7_nn n0 3 = p7_nn n0 2) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hw3 : p7_wrl n0 3 = p7_wrl n0 2) by (unfold p7_wrl, p7_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p7_ovv n0 ov0 3 = 1).
    { unfold p7_ovv. replace (n0 + 3 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p7_nn, p7_cnt in Hn47; lia]. }
    change (2 + 1) with 3. unfold p7_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 2)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 23 (p7_nn n0 2) 1 En) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hn46 : p7_nn n0 2 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p7_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p7_nn n0 2) Bdn ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p7_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p7_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Bdn, Blit, Bsa, B9;
          repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P7SPAN.
  {     lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_gen E _ _ STK sp0 FP _ _ lyc own 32%nat (D + p7_nn n0 2));
      [reflexivity | exact Bdn | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBW a ltac:(lia)) |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p7_nn n0 2) (D + p7_nn n0 2 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?Bdn, ?Blit, ?Bsa, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P7SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 3 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { p_awr_store Edn (D + p7_nn n0 2) HBW. }
    p_frame HFr (D + p7_nn n0 2) (D + p7_nn n0 2 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p7_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p7_nn n0 2) _ 0 1 0 1 0 1%N (SLit 111) 111 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p7_cnt n0 2 = 1) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hc3e : p7_cnt n0 3 = 2) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p7_wrl n0 3)) = p7_cnt n0 3)
      by (unfold p7_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit7]; lia).
    assert (Hn3 : p7_nn n0 3 = p7_nn n0 2 + 1) by (unfold p7_nn; lia).
    assert (Ho3 : p7_ovv n0 ov0 3 = p7_ovv n0 ov0 2).
    { unfold p7_ovv.
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p7_wrl n0 3 = p7_wrl n0 2 ++ [111]).
    { unfold p7_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (2 + 1) with 3. unfold p7_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p7_nn, p7_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 2)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 1) with (D + p7_nn n0 2) by (unfold p7_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { p_awr_store Edn (D + p7_nn n0 2) HBW. }
    p_frame HFr (D + p7_nn n0 2) (D + p7_nn n0 2 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p7_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p7_nn n0 2) _ 0 1 0 1 0 1%N (SLit 111) 111 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p7_cnt n0 2 = 1) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hc3e : p7_cnt n0 3 = 2) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p7_wrl n0 3)) = p7_cnt n0 3)
      by (unfold p7_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit7]; lia).
    assert (Hn3 : p7_nn n0 3 = p7_nn n0 2 + 1) by (unfold p7_nn; lia).
    assert (Ho3 : p7_ovv n0 ov0 3 = p7_ovv n0 ov0 2).
    { unfold p7_ovv.
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p7_wrl n0 3 = p7_wrl n0 2 ++ [111]).
    { unfold p7_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (2 + 1) with 3. unfold p7_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p7_nn, p7_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 2)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 1) with (D + p7_nn n0 2) by (unfold p7_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

Qed.
Lemma p7_it3 : p7_stmt 3.
Proof.
unfold p7_stmt, p7_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & Rn & Rov & Rc & Ri & Rlen & Rcap & Rlit & RA1 & RD & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 30%nat ltac:(unfold disco_nobj; lia)) as HOB. unfold IMG_LO, IMG_TOP in HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 30)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit7 ++ [0])) = 6) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p7_wrl n0 3)) = p7_cnt n0 3)
  by (unfold p7_wrl, p7_cnt; rewrite firstn_length; cbn [length rbn_lit7]; lia).
assert (Hc2 : 0 <= p7_cnt n0 3 <= 2) by (unfold p7_cnt; lia).
assert (HnB : p7_nn n0 3 = n0 + p7_cnt n0 3) by reflexivity.
assert (HnR : 0 <= p7_nn n0 3 <= 47) by (unfold p7_nn, p7_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p7_cnt n0 3) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 6).
{ apply (p_ra_eq (w_H W) memc memE lit 6); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit7 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit7 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
destruct (HRA2 (lit + 3) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 3) mod 8 = 3)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 3) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (3 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 3 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (Rc' : getr regsE 15 = w64 117) by (cbn in Rc; exact Rc).
pose proof (p7_entry fq W regsE memE 3 117 (p7_nn n0 3) (p7_ovv n0 ov0 3) A1 D sv
  Rn Rov Rc' Ri Rlen Rcap Rlit RA1 R22 RD HA1lo HA1hi HA1lit HA1D ltac:(lia) ltac:(lia) HnR HAPP HD63 HAL HSEP HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := E7 regsE (D + p7_nn n0 3) sv sa D) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E5; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D + p7_nn n0 3; sv; sa; D])) E)
  by (unfold E, E5; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + p7_nn n0 3; sv; sa; D])) m)
  by (intros m Hm; unfold E, E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (Edn : ew E 32 = Z_to_bv 64 (D + p7_nn n0 3))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (Esv : ew E 33 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U32 : U E (SOff 32 0) = D + p7_nn n0 3) by (apply (U_atom E 32 _ Edn); lia).
assert (U22 : U E P7BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P7BX P7SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P7SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U32, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U32, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L7)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L7)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P7SPAN.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
  ltac:(intros a (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K1.
rename HG into HG1. clear HF HFr.
assert (En : ew E 23 = Z_to_bv 64 (p7_nn n0 3)) by (rewrite (EE 23%nat 23%bv eq_refl); exact Rn).
assert (Bdn : bv_unsigned (ew E 32) = D + p7_nn n0 3) by (rewrite Edn; apply unsigned_lit_small; lia).
assert (Elit : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact Rlit).
assert (Blit : bv_unsigned (ew E 13) = lit) by (rewrite Elit; apply unsigned_lit_small; lia).
assert (Esa : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (Bsa : bv_unsigned (ew E 34) = sa) by (rewrite Esa; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact RA1).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK P7SPAN.
- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 23 (p7_nn n0 3) 1 En) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hn47 : p7_nn n0 3 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P7SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P7SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 4 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p7_nn n0 4 = p7_nn n0 3) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hw3 : p7_wrl n0 4 = p7_wrl n0 3) by (unfold p7_wrl, p7_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p7_ovv n0 ov0 4 = 1).
    { unfold p7_ovv. replace (n0 + 4 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p7_nn, p7_cnt in Hn47; lia]. }
    change (3 + 1) with 4. unfold p7_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 3)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p7_nn n0 4 = p7_nn n0 3) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hw3 : p7_wrl n0 4 = p7_wrl n0 3) by (unfold p7_wrl, p7_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p7_ovv n0 ov0 4 = 1).
    { unfold p7_ovv. replace (n0 + 4 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p7_nn, p7_cnt in Hn47; lia]. }
    change (3 + 1) with 4. unfold p7_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 3)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 23 (p7_nn n0 3) 1 En) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hn46 : p7_nn n0 3 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p7_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p7_nn n0 3) Bdn ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p7_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p7_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Bdn, Blit, Bsa, B9;
          repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P7SPAN.
  {     lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_gen E _ _ STK sp0 FP _ _ lyc own 32%nat (D + p7_nn n0 3));
      [reflexivity | exact Bdn | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBW a ltac:(lia)) |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p7_nn n0 3) (D + p7_nn n0 3 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?Bdn, ?Blit, ?Bsa, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P7SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 4 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { p_awr_store Edn (D + p7_nn n0 3) HBW. }
    p_frame HFr (D + p7_nn n0 3) (D + p7_nn n0 3 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p7_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p7_nn n0 3) _ 0 1 0 1 0 1%N (SLit 117) 117 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p7_cnt n0 3 = 2) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hc3e : p7_cnt n0 4 = 3) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p7_wrl n0 4)) = p7_cnt n0 4)
      by (unfold p7_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit7]; lia).
    assert (Hn3 : p7_nn n0 4 = p7_nn n0 3 + 1) by (unfold p7_nn; lia).
    assert (Ho3 : p7_ovv n0 ov0 4 = p7_ovv n0 ov0 3).
    { unfold p7_ovv.
      replace (n0 + 4 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p7_wrl n0 4 = p7_wrl n0 3 ++ [117]).
    { unfold p7_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (3 + 1) with 4. unfold p7_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p7_nn, p7_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 3)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 2) with (D + p7_nn n0 3) by (unfold p7_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { p_awr_store Edn (D + p7_nn n0 3) HBW. }
    p_frame HFr (D + p7_nn n0 3) (D + p7_nn n0 3 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p7_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p7_nn n0 3) _ 0 1 0 1 0 1%N (SLit 117) 117 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p7_cnt n0 3 = 2) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hc3e : p7_cnt n0 4 = 3) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p7_wrl n0 4)) = p7_cnt n0 4)
      by (unfold p7_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit7]; lia).
    assert (Hn3 : p7_nn n0 4 = p7_nn n0 3 + 1) by (unfold p7_nn; lia).
    assert (Ho3 : p7_ovv n0 ov0 4 = p7_ovv n0 ov0 3).
    { unfold p7_ovv.
      replace (n0 + 4 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p7_wrl n0 4 = p7_wrl n0 3 ++ [117]).
    { unfold p7_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (3 + 1) with 4. unfold p7_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p7_nn, p7_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 3)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 2) with (D + p7_nn n0 3) by (unfold p7_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

Qed.
Lemma p7_it4 : p7_stmt 4.
Proof.
unfold p7_stmt, p7_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & Rn & Rov & Rc & Ri & Rlen & Rcap & Rlit & RA1 & RD & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 30%nat ltac:(unfold disco_nobj; lia)) as HOB. unfold IMG_LO, IMG_TOP in HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 30)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit7 ++ [0])) = 6) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p7_wrl n0 4)) = p7_cnt n0 4)
  by (unfold p7_wrl, p7_cnt; rewrite firstn_length; cbn [length rbn_lit7]; lia).
assert (Hc2 : 0 <= p7_cnt n0 4 <= 3) by (unfold p7_cnt; lia).
assert (HnB : p7_nn n0 4 = n0 + p7_cnt n0 4) by reflexivity.
assert (HnR : 0 <= p7_nn n0 4 <= 47) by (unfold p7_nn, p7_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p7_cnt n0 4) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 6).
{ apply (p_ra_eq (w_H W) memc memE lit 6); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit7 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit7 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
destruct (HRA2 (lit + 4) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 4) mod 8 = 4)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 4) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (4 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 4 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (Rc' : getr regsE 15 = w64 116) by (cbn in Rc; exact Rc).
pose proof (p7_entry fq W regsE memE 4 116 (p7_nn n0 4) (p7_ovv n0 ov0 4) A1 D sv
  Rn Rov Rc' Ri Rlen Rcap Rlit RA1 R22 RD HA1lo HA1hi HA1lit HA1D ltac:(lia) ltac:(lia) HnR HAPP HD63 HAL HSEP HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := E7 regsE (D + p7_nn n0 4) sv sa D) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E5; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D + p7_nn n0 4; sv; sa; D])) E)
  by (unfold E, E5; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + p7_nn n0 4; sv; sa; D])) m)
  by (intros m Hm; unfold E, E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (Edn : ew E 32 = Z_to_bv 64 (D + p7_nn n0 4))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (Esv : ew E 33 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U32 : U E (SOff 32 0) = D + p7_nn n0 4) by (apply (U_atom E 32 _ Edn); lia).
assert (U22 : U E P7BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P7BX P7SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P7SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U32, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U32, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L7)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L7)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P7SPAN.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
  ltac:(intros a (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K1.
rename HG into HG1. clear HF HFr.
assert (En : ew E 23 = Z_to_bv 64 (p7_nn n0 4)) by (rewrite (EE 23%nat 23%bv eq_refl); exact Rn).
assert (Bdn : bv_unsigned (ew E 32) = D + p7_nn n0 4) by (rewrite Edn; apply unsigned_lit_small; lia).
assert (Elit : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact Rlit).
assert (Blit : bv_unsigned (ew E 13) = lit) by (rewrite Elit; apply unsigned_lit_small; lia).
assert (Esa : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (Bsa : bv_unsigned (ew E 34) = sa) by (rewrite Esa; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact RA1).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK P7SPAN.
- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 23 (p7_nn n0 4) 1 En) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hn47 : p7_nn n0 4 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P7SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P7SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 5 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p7_nn n0 5 = p7_nn n0 4) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hw3 : p7_wrl n0 5 = p7_wrl n0 4) by (unfold p7_wrl, p7_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p7_ovv n0 ov0 5 = 1).
    { unfold p7_ovv. replace (n0 + 5 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p7_nn, p7_cnt in Hn47; lia]. }
    change (4 + 1) with 5. unfold p7_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 4)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p7_nn n0 5 = p7_nn n0 4) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hw3 : p7_wrl n0 5 = p7_wrl n0 4) by (unfold p7_wrl, p7_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p7_ovv n0 ov0 5 = 1).
    { unfold p7_ovv. replace (n0 + 5 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p7_nn, p7_cnt in Hn47; lia]. }
    change (4 + 1) with 5. unfold p7_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 4)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 23 (p7_nn n0 4) 1 En) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hn46 : p7_nn n0 4 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p7_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p7_nn n0 4) Bdn ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p7_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p7_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Bdn, Blit, Bsa, B9;
          repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P7SPAN.
  {     lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_gen E _ _ STK sp0 FP _ _ lyc own 32%nat (D + p7_nn n0 4));
      [reflexivity | exact Bdn | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBW a ltac:(lia)) |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p7_nn n0 4) (D + p7_nn n0 4 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?Bdn, ?Blit, ?Bsa, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P7SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 5 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { p_awr_store Edn (D + p7_nn n0 4) HBW. }
    p_frame HFr (D + p7_nn n0 4) (D + p7_nn n0 4 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p7_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p7_nn n0 4) _ 0 1 0 1 0 1%N (SLit 116) 116 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p7_cnt n0 4 = 3) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hc3e : p7_cnt n0 5 = 4) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p7_wrl n0 5)) = p7_cnt n0 5)
      by (unfold p7_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit7]; lia).
    assert (Hn3 : p7_nn n0 5 = p7_nn n0 4 + 1) by (unfold p7_nn; lia).
    assert (Ho3 : p7_ovv n0 ov0 5 = p7_ovv n0 ov0 4).
    { unfold p7_ovv.
      replace (n0 + 5 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      replace (n0 + 4 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p7_wrl n0 5 = p7_wrl n0 4 ++ [116]).
    { unfold p7_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (4 + 1) with 5. unfold p7_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p7_nn, p7_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 4)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 3) with (D + p7_nn n0 4) by (unfold p7_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7).
    { p_awr_store Edn (D + p7_nn n0 4) HBW. }
    p_frame HFr (D + p7_nn n0 4) (D + p7_nn n0 4 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p7_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p7_nn n0 4) _ 0 1 0 1 0 1%N (SLit 116) 116 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p7_cnt n0 4 = 3) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hc3e : p7_cnt n0 5 = 4) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p7_wrl n0 5)) = p7_cnt n0 5)
      by (unfold p7_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit7]; lia).
    assert (Hn3 : p7_nn n0 5 = p7_nn n0 4 + 1) by (unfold p7_nn; lia).
    assert (Ho3 : p7_ovv n0 ov0 5 = p7_ovv n0 ov0 4).
    { unfold p7_ovv.
      replace (n0 + 5 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      replace (n0 + 4 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p7_wrl n0 5 = p7_wrl n0 4 ++ [116]).
    { unfold p7_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (4 + 1) with 5. unfold p7_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p7_nn, p7_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 4)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 3) with (D + p7_nn n0 4) by (unfold p7_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

Qed.
Lemma p7_it5 : p7_stmt 5.
Proof.
unfold p7_stmt, p7_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & Rn & Rov & Rc & Ri & Rlen & Rcap & Rlit & RA1 & RD & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (pa_obj_img 30%nat ltac:(unfold disco_nobj; lia)) as HOB. unfold IMG_LO, IMG_TOP in HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 30)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit7 ++ [0])) = 6) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p7_wrl n0 5)) = p7_cnt n0 5)
  by (unfold p7_wrl, p7_cnt; rewrite firstn_length; cbn [length rbn_lit7]; lia).
assert (Hc2 : 0 <= p7_cnt n0 5 <= 4) by (unfold p7_cnt; lia).
assert (HnB : p7_nn n0 5 = n0 + p7_cnt n0 5) by reflexivity.
assert (HnR : 0 <= p7_nn n0 5 <= 47) by (unfold p7_nn, p7_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p7_cnt n0 5) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 6).
{ apply (p_ra_eq (w_H W) memc memE lit 6); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit7 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit7 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
destruct (HRA2 (lit + 5) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 5) mod 8 = 5)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 5) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (5 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 5 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (Rc' : getr regsE 15 = w64 41) by (cbn in Rc; exact Rc).
pose proof (p7_entry fq W regsE memE 5 41 (p7_nn n0 5) (p7_ovv n0 ov0 5) A1 D sv
  Rn Rov Rc' Ri Rlen Rcap Rlit RA1 R22 RD HA1lo HA1hi HA1lit HA1D ltac:(lia) ltac:(lia) HnR HAPP HD63 HAL HSEP HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := E7 regsE (D + p7_nn n0 5) sv sa D) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E5; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D + p7_nn n0 5; sv; sa; D])) E)
  by (unfold E, E5; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D + p7_nn n0 5; sv; sa; D])) m)
  by (intros m Hm; unfold E, E5; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E5; apply ew_Eimg_Ereg_nat; exact Hm).
assert (Edn : ew E 32 = Z_to_bv 64 (D + p7_nn n0 5))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (Esv : ew E 33 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U32 : U E (SOff 32 0) = D + p7_nn n0 5) by (apply (U_atom E 32 _ Edn); lia).
assert (U22 : U E P7BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P7BX P7SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P7SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U32, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U32, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L7)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L7)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P7SPAN.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
  ltac:(intros a (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K1.
rename HG into HG1. clear HF HFr.
assert (En : ew E 23 = Z_to_bv 64 (p7_nn n0 5)) by (rewrite (EE 23%nat 23%bv eq_refl); exact Rn).
assert (Bdn : bv_unsigned (ew E 32) = D + p7_nn n0 5) by (rewrite Edn; apply unsigned_lit_small; lia).
assert (Elit : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact Rlit).
assert (Blit : bv_unsigned (ew E 13) = lit) by (rewrite Elit; apply unsigned_lit_small; lia).
assert (Esa : ew E 34 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (Bsa : bv_unsigned (ew E 34) = sa) by (rewrite Esa; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact RA1).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
psrr_branch_tok RUN BR HS SHOK P7SPAN.
- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 23 (p7_nn n0 5) 1 En) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hn47 : p7_nn n0 5 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P7SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ 0 0 HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P7SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 6 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7X).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p7_nn n0 6 = p7_nn n0 5) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hw3 : p7_wrl n0 6 = p7_wrl n0 5) by (unfold p7_wrl, p7_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p7_ovv n0 ov0 6 = 1).
    { unfold p7_ovv. replace (n0 + 6 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p7_nn, p7_cnt in Hn47; lia]. }
    change (5 + 1) with 6. unfold p7_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 5)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7X).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    p_frame HFr 0 0 Edn Elit Esa E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p7_nn n0 6 = p7_nn n0 5) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hw3 : p7_wrl n0 6 = p7_wrl n0 5) by (unfold p7_wrl, p7_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p7_ovv n0 ov0 6 = 1).
    { unfold p7_ovv. replace (n0 + 6 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p7_nn, p7_cnt in Hn47; lia]. }
    change (5 + 1) with 6. unfold p7_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 5)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En; reflexivity|].
    split; [rewrite Qov; reflexivity|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

- rewrite branch_geu_U in Hc. rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 23 (p7_nn n0 5) 1 En) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hn46 : p7_nn n0 5 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p7_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p7_nn n0 5) Bdn ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p7_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p7_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Bdn, Blit, Bsa, B9;
          repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P7SPAN.
  {     lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_gen E _ _ STK sp0 FP _ _ lyc own 32%nat (D + p7_nn n0 5));
      [reflexivity | exact Bdn | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBW a ltac:(lia)) |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    apply awr_ok_nil. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p7_nn n0 5) (D + p7_nn n0 5 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?Bdn, ?Blit, ?Bsa, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P7SPAN.
  +
    p_efact HS 33%nat Esv Gsv.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 33 sv Gsv) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 33%nat (mkAF 6 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Gsv, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7X).
    { p_awr_store Edn (D + p7_nn n0 5) HBW. }
    p_frame HFr (D + p7_nn n0 5) (D + p7_nn n0 5 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p7_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p7_nn n0 5) _ 0 1 0 1 0 1%N (SLit 41) 41 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p7_cnt n0 5 = 4) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hc3e : p7_cnt n0 6 = 5) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p7_wrl n0 6)) = p7_cnt n0 6)
      by (unfold p7_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit7]; lia).
    assert (Hn3 : p7_nn n0 6 = p7_nn n0 5 + 1) by (unfold p7_nn; lia).
    assert (Ho3 : p7_ovv n0 ov0 6 = p7_ovv n0 ov0 5).
    { unfold p7_ovv.
      replace (n0 + 6 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      replace (n0 + 5 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p7_wrl n0 6 = p7_wrl n0 5 ++ [41]).
    { unfold p7_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (5 + 1) with 6. unfold p7_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p7_nn, p7_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 5)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 4) with (D + p7_nn n0 5) by (unfold p7_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.
  +
    paj_run_to_tok RUNTO HS HJ SHOK P7SPAN (AF_reac_box_name + RBN_L7X).
    { p_awr_store Edn (D + p7_nn n0 5) HBW. }
    p_frame HFr (D + p7_nn n0 5) (D + p7_nn n0 5 + 1) Edn Elit Esa E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p7_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 32%nat (D + p7_nn n0 5) _ 0 1 0 1 0 1%N (SLit 41) 41 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite Edn; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (23%bv : bv 5) Qn. prreg HS (12%bv : bv 5) Qov. prreg HS (15%bv : bv 5) Qc.
    prreg HS (21%bv : bv 5) Qi. prreg HS (14%bv : bv 5) Qlen. prreg HS (11%bv : bv 5) Qcap.
    prreg HS (13%bv : bv 5) Qlit. prreg HS (9%bv : bv 5) QA1. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P7KEPT HS ltac:(cbn [extK]; p_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 21; 23]) by
        (apply p7_keep_of;
         [ exact HKr
         | apply (p_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qcap Rcap)
         | apply (p_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 6)
             ltac:(apply bv_eq; vm_compute; reflexivity) Qlen Rlen) ]) end.
    assert (Hc2e : p7_cnt n0 5 = 4) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hc3e : p7_cnt n0 6 = 5) by (unfold p7_nn, p7_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p7_wrl n0 6)) = p7_cnt n0 6)
      by (unfold p7_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit7]; lia).
    assert (Hn3 : p7_nn n0 6 = p7_nn n0 5 + 1) by (unfold p7_nn; lia).
    assert (Ho3 : p7_ovv n0 ov0 6 = p7_ovv n0 ov0 5).
    { unfold p7_ovv.
      replace (n0 + 6 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      replace (n0 + 5 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p7_nn, p7_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p7_wrl n0 6 = p7_wrl n0 5 ++ [41]).
    { unfold p7_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p7_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (5 + 1) with 6. unfold p7_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p7_nn, p7_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p7_wrl n0 5)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p7_nn, p7_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 4) with (D + p7_nn n0 5) by (unfold p7_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Qn, En, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Qov; rewrite (EE 12%nat 12%bv eq_refl); exact Rov|].
    split; [rewrite Qc; cbn [rbn_lit7 nth Z.to_nat]; reflexivity|].
    split; [rewrite Qi; reflexivity|].
    split; [rewrite Qlen; reflexivity|].
    split; [rewrite Qcap; reflexivity|].
    split; [rewrite Qlit, Elit; reflexivity|].
    split; [rewrite QA1; rewrite (EE 9%nat 9%bv eq_refl); exact RA1|].
    split.
    { apply (p_val_mem_eq (w_H W) memE _ (A1 + 120) 8%nat D); [|exact RD].
      intros x Hx. change (Z.of_nat 8%nat) with 8 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    rewrite Q22, E22. reflexivity.

Qed.
Lemma p7_all : forall (regsE : bvmap 5 word) memE mdE,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k ->
  p7_pkg 1 regsE memE ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L7) regsE memE mdE)
    (p7_next 6).
Proof.
intros regsE memE mdE HJ HP.
eapply SRr_bind; [exact (p7_it1 regsE memE mdE HJ HP)|].
intros W2 c2 Hle2 Hx2. change (1 + 1) with 2 in Hx2.
destruct Hx2 as (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2).
assert (Hpc2 : (if (2 : Z) <=? 5 then 16020 else 16132) = AF_reac_box_name + RBN_L7)
  by reflexivity.
rewrite Hpc2.
replace (BASE + (AF_reac_box_name + RBN_L7)) with (BASE + AF_reac_box_name + RBN_L7) by lia.
eapply SRr_bind; [exact (p7_it2 regs2 mem2 md2 HJ2 HP2)|].
intros W3 c3 Hle3 Hx3. change (2 + 1) with 3 in Hx3.
destruct Hx3 as (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3).
assert (Hpc3 : (if (3 : Z) <=? 5 then 16020 else 16132) = AF_reac_box_name + RBN_L7)
  by reflexivity.
rewrite Hpc3.
replace (BASE + (AF_reac_box_name + RBN_L7)) with (BASE + AF_reac_box_name + RBN_L7) by lia.
eapply SRr_bind; [exact (p7_it3 regs3 mem3 md3 HJ3 HP3)|].
intros W4 c4 Hle4 Hx4. change (3 + 1) with 4 in Hx4.
destruct Hx4 as (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4).
assert (Hpc4 : (if (4 : Z) <=? 5 then 16020 else 16132) = AF_reac_box_name + RBN_L7)
  by reflexivity.
rewrite Hpc4.
replace (BASE + (AF_reac_box_name + RBN_L7)) with (BASE + AF_reac_box_name + RBN_L7) by lia.
eapply SRr_bind; [exact (p7_it4 regs4 mem4 md4 HJ4 HP4)|].
intros W5 c5 Hle5 Hx5. change (4 + 1) with 5 in Hx5.
destruct Hx5 as (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5).
assert (Hpc5 : (if (5 : Z) <=? 5 then 16020 else 16132) = AF_reac_box_name + RBN_L7)
  by reflexivity.
rewrite Hpc5.
replace (BASE + (AF_reac_box_name + RBN_L7)) with (BASE + AF_reac_box_name + RBN_L7) by lia.
pose proof (p7_it5 regs5 mem5 md5 HJ5 HP5) as HR.
change (5 + 1) with 6 in HR. exact HR.
Qed.
Lemma p7_fin_run : forall (mdc : Model) (nF ovF : Z) (wr : list Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 23 = w64 n0 -> getr regs 12 = w64 ov0 -> getr regs 15 = w64 32 ->
  getr regs 21 = w64 1 -> getr regs 14 = w64 6 -> getr regs 11 = w64 48 ->
  getr regs 13 = w64 (VAL (A_OBJ 30)) -> getr regs 9 = w64 A1 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A1 + 120) 8 D -> getr regs 22 = w64 SHADOW_OFF ->
  p7_nn n0 6 = nF -> p7_ovv n0 ov0 6 = ovF -> p7_wrl n0 6 = wr ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L7) regs memc mdc)
    (rbn_lpost B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L7X [5; 10; 12; 15; 16; 17; 21; 23]
       D n0 wr [(23, nF); (12, ovF)]).
Proof.
intros mdc nF ovF wr HJ Rn Rov Rc Ri Rlen Rcap Rlit RA1 RD RSB HnF HovF HwF.
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
eapply SRr_mono.
{ apply (p7_all regs memc mdc HJ).
  unfold p7_pkg. split; [intros a Ha Hn; reflexivity|].
  split.
  { unfold p7_wrl, p7_cnt. rewrite Z.min_l by lia.
    intros j Hj. vm_compute in Hj. lia. }
  split; [intros a Ha; exact (proj2 (HBW a Ha))|].
  split; [intros r Hr Hnin; reflexivity|].
  split; [unfold p7_nn, p7_cnt; rewrite Z.min_l by lia; rewrite Z.add_0_r; exact Rn|].
  split; [unfold p7_ovv; replace (n0 + 1 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; lia);
          exact Rov|].
  split; [cbn [Z.to_nat rbn_lit7 nth]; exact Rc|].
  split; [exact Ri|]. split; [exact Rlen|]. split; [exact Rcap|]. split; [exact Rlit|].
  split; [exact RA1|]. split; [exact RD | exact RSB]. }
intros W2 c2 Hle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2).
destruct HP2 as (HEQ & HWR & HPR & HKEEP & Qn & Qov & Qc & Qi & Qlen & Qcap & Qlit & QA1 & QD & QSB).
unfold rbn_lpost. split; [reflexivity|]. exists regs2, mem2, md2.
split.
{ unfold cfg_at, w64. cbn [Z.leb Z.compare].
  replace (BASE + AF_reac_box_name + RBN_L7X) with (BASE + 16132)
    by (unfold AF_reac_box_name, RBN_L7X; lia).
  reflexivity. }
split; [exact HJ2|]. split; [exact HKEEP|].
split.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
  - replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Qn, HnF. reflexivity.
  - replace (Z_to_bv 5 12) with (12%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Qov, HovF. reflexivity. }
rewrite <- HwF. split; [exact HEQ | exact HWR].
Qed.
End S7.
Theorem rbn_L7_fits_holds : rbn_L7_fits B.
Proof.
unfold rbn_L7_fits, rbn_L7_run.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 Hfit
  HJ HSRC HAL HA1lo HA1hi HA1lit HBUF HSEP RD HA1D HN0 HOV0 Rn Rov Rc Ri Rlen Rcap Rlit RA1 RSB.
eapply p7_fin_run; try eassumption.
all: first
  [ solve [unfold p7_nn, p7_cnt; lia]
  | solve [unfold p7_ovv; replace (n0 + 6 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; lia);
           reflexivity]
  | solve [unfold p7_wrl, p7_cnt; replace (Z.min (6 - 1) (47 - n0)) with 5 by lia;
           reflexivity] ].
Qed.
Theorem rbn_L7_ovf_holds : rbn_L7_ovf B.
Proof.
unfold rbn_L7_ovf, rbn_L7_run.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 Hovf
  HJ HSRC HAL HA1lo HA1hi HA1lit HBUF HSEP RD HA1D HN0 HOV0 Rn Rov Rc Ri Rlen Rcap Rlit RA1 RSB.
eapply p7_fin_run; try eassumption.
all: first
  [ solve [unfold p7_nn, p7_cnt; lia]
  | solve [unfold p7_ovv; replace (n0 + 6 - 1 <=? 47) with false by (symmetry; apply Z.leb_gt; lia);
           reflexivity]
  | solve [unfold p7_wrl, p7_cnt; f_equal; f_equal; lia] ].
Qed.
End h.
End f.
End d.
