(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths changed; 599 of its 833 lines of code are new or changed and 2508 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/RecStubU.v, with its module paths and module names changed; 444 of its 497 lines of code are new or changed and 780 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItCK.v, with its module names changed; 342 of its 427 lines of code are new or changed and 412 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel CommandFP SlotSpec
  SlotRuns check_reply_c check_arity_c check_reply_answer_c rec_shape_of_c SlotItCK0 SlotItCK.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require SlotWords SlotWordsRun strspn_c strcspn_c
  memcpy_c.
Import ListNotations.
Local Open Scope Z_scope.

(* seg_b2 (ubsan): from the third malloc's return (stB, pc 0x14200) to check_words' entry (stBW, pc 0x14bac): the
   splitter (SlotWordsRun.sw_run), then check_reply and check_arity (SlotItCK.ck_evt_holds), on the memory
   normalized to the task's addresses, lifted into SR by SlotItBase.sr_cj. *)

(* The locals at sp: LOC1 k (k stored at sp + 16) is LOC0 with the bytes of k. *)
Lemma q3_loc1_loc0 : forall m a k, rw_cells rsegs m a (LOC1 k) -> rw_cells rsegs m a (LOC0 (le8 (Z_to_bv 64 k))).
Proof.
  intros m a k [[W Bt] Wr]. unfold LOC1, LOC0 in *. split; [split|].
  - cbn [cells_wf cell_wf]. rewrite length_le8. tauto.
  - cbn [cells_bytes cbytes] in *. exact Bt.
  - cbn [cells_size csize] in *. exact Wr.
Qed.

Lemma q3_loc0_loc1 : forall m a k, rw_cells rsegs m a (LOC0 (le8 (Z_to_bv 64 k))) -> rw_cells rsegs m a (LOC1 k).
Proof.
  intros m a k [[W Bt] Wr]. unfold LOC1, LOC0 in *. split; [split|].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes] in *. exact Bt.
  - cbn [cells_size csize] in *. exact Wr.
Qed.

(* The splitter, then check_reply and check_arity, as one run on the normalized memory m0: the premises of
   SlotItCK0.ck_spec, the splitter's three callee contracts and the memory facts of SlotWordsRun.sw_run. *)
Section E.
Variables (sp gp tp s2 s3 s5 s6 s7 s10 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
  (lo src len text copy arr : Z) (M : list byte) (jsv : list byte) (can : word).

Notation SP := (bv_unsigned sp).
Notation L0w := (strnlen_res len M).
Notation ws := (Verbs.words (Verbs.line M)).
Notation W0 := [(text, text + strnlen_res len M + 1); (copy, copy + strnlen_res len M + 1);
                (arr, arr + arr_size (strnlen_res len M)); (bv_unsigned sp - 96, bv_unsigned sp + 56)].

Hypothesis H_lo : 0x54f98 <= lo.
Hypothesis H_LOS : lo + 6000 <= SP.
Hypothesis H_SPH : SP + 160 <= 2 ^ 63.
Hypothesis H_TS : SP + 160 <= TASK_SIZE.
Hypothesis H_SP8 : SP mod 8 = 0.
Hypothesis H_len : 0 <= len <= 8192.
Hypothesis H_src : 0 <= src /\ src + len <= lo.
Hypothesis H_L0 : 0 <= L0w <= len.
Hypothesis H_tx : 0 < text /\ text + L0w + 1 <= lo.
Hypothesis H_cp : 0 < copy /\ copy + L0w + 1 <= lo.
Hypothesis H_ar : 0 < arr /\ arr + arr_size L0w <= lo.
Hypothesis H_AS : arr_size L0w = 8 * (L0w / 2) + 16.
Hypothesis CRC : check_reply_contract.
Hypothesis CAC : check_arity_contract.
Hypothesis H_M : Z.of_nat (length M) = len.
Hypothesis H_txi : text + L0w + 1 <= 0x10000 \/ 0x54f98 <= text.
Hypothesis H_cpi : copy + L0w + 1 <= 0x10000 \/ 0x54f98 <= copy.
Hypothesis H_ari : arr + arr_size L0w <= 0x10000 \/ 0x54f98 <= arr.
Hypothesis H_d1 : text + L0w + 1 <= copy \/ copy + L0w + 1 <= text.
Hypothesis H_d2 : arr + arr_size L0w <= text \/ text + L0w + 1 <= arr.
Hypothesis H_d3 : arr + arr_size L0w <= copy \/ copy + L0w + 1 <= arr.
Hypothesis H_d4 : src + len <= text \/ text + L0w + 1 <= src.
Hypothesis H_al : text mod 8 = 0 /\ arr mod 8 = 0 /\ lo mod 8 = 0.
Hypothesis H_fc : frm0 fc.
Hypothesis H_tk : MemNorm.task_mem rsegs m0.
Hypothesis H_gg : rw_cells rsegs m0 GOT_GUARD [C8 (Z_to_bv 64 GUARD)].
Hypothesis H_gu : rw_cells rsegs m0 GUARD [C8 can].
Hypothesis H_cs : forall a, copy + L0w + 1 <= a < 8 * ((copy + L0w + 1 + 7) / 8) -> mbyte rsegs m0 a <> None.

Variables (ans rep : word) (xr slack xa : list byte) (nc fn0 q : Z).
Hypothesis H_grec : bytes_at rsegs m0 GOT_GREC (le8 (Z_to_bv 64 G_REC)).
Hypothesis H_ans : bytes_at rsegs m0 (G_REC + REC_ANSWER) (le8 ans).
Hypothesis H_nr : bytes_at rsegs m0 (G_REC + REC_NREPLIES) (le4 (Z_to_bv 64 1)).
Hypothesis H_rp : bytes_at rsegs m0 (G_REC + REC_REPLY) (le8 rep).
Hypothesis H_rs : bytes_at rsegs m0 (G_REC + REC_REPLY_SIZE) (le8 (Z_to_bv 64 (Z.of_nat (length xr) + 1))).
Hypothesis H_sh : bytes_at rsegs m0 G_SHAPES g_shapes_bytes.
Hypothesis H_rnz : bv_unsigned rep <> 0.
Hypothesis H_rb : bytes_at rsegs m0 (bv_unsigned rep) (xr ++ NUL :: slack).
Hypothesis H_xr : ~ In NUL xr.
Hypothesis H_sl : (- (bv_unsigned rep + Z.of_nat (length xr) + 1)) mod 8 <= Z.of_nat (length slack).
Hypothesis H_ro : forall i, 0 <= i < Z.of_nat (length xr) + 1 + Z.of_nat (length slack) ->
  Frame.outside W0 (bv_unsigned rep + i) /\ bv_unsigned rep + i < lo.
Hypothesis H_ab : bv_unsigned ans <> 0 -> cstr_at m0 (bv_unsigned ans) xa /\
  forall i, 0 <= i < Z.of_nat (length xa) + 1 -> Frame.outside W0 (bv_unsigned ans + i) /\ bv_unsigned ans + i < lo.
Hypothesis H_aok : answer_ok ans xr xa (Z.of_nat (length ws)) (nth 0 ws []).
Hypothesis H_rok : reply_ok (Z.of_nat (length ws)) (nth 0 ws []) xr.
Hypothesis H_par : bytes_at rsegs m0 G_PARSED g_parsed_bytes.
Hypothesis H_nc : 0 <= nc <= 16 /\ bytes_at rsegs m0 (G_REC + REC_NCALLS) (le4 (Z_to_bv 64 nc)).
Hypothesis H_fn : 0 < nc -> 0 <= fn0 < 26 /\ bytes_at rsegs m0 (G_REC + REC_CALLS + CALL_FN) (le4 (Z_to_bv 64 fn0)).
Hypothesis H_gq : bytes_at rsegs m0 GOT_GQUIT (le8 (Z_to_bv 64 G_QUIT)).
Hypothesis H_q : 0 <= q < 2 ^ 32 /\ bytes_at rsegs m0 G_QUIT (le4 (Z_to_bv 64 q)).
Hypothesis H_aro : arity_ok (Z.of_nat (length ws)) (nth 0 ws []) q nc fn0.
Hypothesis SSPN : U.Prog.strspn_c.strspn_contract.
Hypothesis SCSPN : U.Prog.strcspn_c.strcspn_contract.
Hypothesis MEMC : U.Prog.memcpy_c.memcpy_contract.

Lemma q3_evt : forall ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' jt jc ja jw,
  mem_inv rsegs m0 -> stk rsegs m0 lo SP ->
  bytes_at rsegs m0 src M ->
  u8arr rsegs m0 text jt -> length jt = Z.to_nat (L0w + 1) ->
  u8arr rsegs m0 copy jc -> length jc = Z.to_nat (L0w + 1) ->
  u8arr rsegs m0 arr ja -> length ja = Z.to_nat (arr_size L0w) ->
  rw_cells rsegs m0 SP (LOC0 jsv) ->
  rw_cells rsegs m0 (SP + 24) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); CB 16 jw] ->
  evt rsegs (w_post sp gp tp s2 s3 s5 s6 s7 s10 m0 lo src len text copy arr M jsv)
    (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len) (Z_to_bv 64 arr) a1' a2' a3' a4'
       a5' a6' a7' s2 s3 (Z_to_bv 64 L0w) s5 s6 s7 (Z_to_bv 64 MASK) (Z_to_bv 64 32) s10 (Z_to_bv 64 (2 ^ 64 - 1))
       t3' t4' t5' t6') F (Z_to_bv 64 0x14200) fc None m0 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' jt jc ja jw
    MI ST SRC TX LT CP LC AR LA FR0 FR1.
  assert (G1 : bytes_at rsegs m0 U.Prog.strspn_c.SSP_GOT (le8 (Z_to_bv 64 U.Prog.strspn_c.SSP_GUARD))).
  { pose proof (ck_cells_bytes _ _ _ H_gg) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (G2 : bytes_at rsegs m0 U.Prog.strspn_c.SSP_GUARD (le8 can)).
  { pose proof (ck_cells_bytes _ _ _ H_gu) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof H_al as (AL1 & AL2 & AL3).
  eapply evt_cut.
  { eapply SlotWordsRun.sw_run with (lo := lo) (M := M) (text := text) (copy := copy) (can := can) (jsv := jsv)
      (jt := jt) (jc := jc) (ja := ja) (jw := jw).
    all: first [ exact MI | exact ST | exact SRC | exact TX | exact LT | exact CP | exact LC | exact AR | exact LA
               | exact G1 | exact G2 | exact FR0 | exact FR1 | exact SSPN | exact SCSPN | exact MEMC | exact H_M
               | exact H_txi | exact H_cpi | exact H_ari | exact H_d1 | exact H_d2 | exact H_d3 | exact H_d4
               | exact H_src | exact H_L0 | exact H_tx | exact H_cp | exact H_ar | exact H_AS | exact H_len
               | exact AL2 | exact H_lo | lia ]. }
  intros ms1 H1.
  exact (ck_evt_holds sp gp tp s2 s3 s5 s6 s7 s10 F fc m0 lo src len text copy arr M jsv can ans rep xr slack xa nc fn0 q
    H_lo H_LOS H_SPH H_TS H_SP8 H_len H_src H_L0 H_tx H_cp H_ar H_AS CRC CAC H_M H_txi H_cpi H_ari H_d1 H_d2 H_d3 H_d4
    H_al H_fc H_tk H_gg H_gu H_cs H_grec H_ans H_nr H_rp H_rs H_sh H_rnz H_rb H_xr H_sl H_ro H_ab H_aok H_rok H_par
    H_nc H_fn H_gq H_q H_aro ms1 H1).
Qed.

End E.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL0g YL01 YL00 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import AllocSI AllocGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU SlotSpec SlotGlue
  SlotRuns SlotCallees SlotIter SlotEnd SlotItBase SlotItSt verbs_receive_c send_message_c CommandB VerbsB
  CommandModel SlotItA SlotItE SlotItB SlotItBW SlotItB3qh SlotItB3p SlotItProof.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Slot SlotInv SlotRec RecTail RecAnsB
  RecAns send_message VerbsMem chain_words SlotItHP.

Ltac q3_cz := apply Z.leb_le; vm_compute; reflexivity.

Lemma q3_ha1 {rc : RunCeil} : forall c l a, 0 <= l -> 4096 <= c -> c + (l + 1) <= alloc_ceiling -> c + l + 1 <= a ->
  a < c + l + 1 + 8 ->
  0 <= a < TASK_SIZE.
Proof. intros c l a H0 H1 H2 H3 H4. pose proof alloc_ceiling_val. unfold TASK_SIZE. lia. Qed.

Lemma q3_ha2 : forall c l a, 0 <= l -> (c + (l + 1) <= 0x10000 \/ 0x55000 <= c) ->
  c + l + 1 <= a < 8 * ((c + l + 1 + 7) / 8) -> ~ (0x10000 <= a < 0x22000).
Proof.
  intros c l a H0 [H|H] [H1 H2]; [pose proof (q3h_r8 (c + l + 1) 0x10000 ltac:(lia) eq_refl); lia | lia].
Qed.

(* From stB's facts (SlotItB3p.SB) to check_words' entry: q3_evt on the memory normalized to the task's addresses,
   then SlotItB3p.b3_post_u back to the real memory, lifted into SR by SlotItBase.sr_cj. *)
Section Q3.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : Slot.frame_given_u B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (SlotInv.FB S).

Lemma q3_evtS : check_reply_contract -> check_arity_contract -> U.Prog.memcpy_c.memcpy_contract ->
  U.Prog.strspn_c.strspn_contract -> U.Prog.strcspn_c.strcspn_contract ->
  forall fx L A regs mem md O R1 x quit text copy arr jw m p n R0,
  SB B API S rg mem0 md0 L0 A0 p0 n0 pl fx L A regs mem md O R1 x quit text copy arr jw m p n R0 ->
  Exec.evt rsegs (SlotItCK0.w_post (Z_to_bv 64 FB) (reg_get regs 3) (reg_get regs 4) (reg_get regs 18)
      (reg_get regs 19) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 26)
      (normalize_cj rsegs mem) (S - SLOT_STACK) (m_src p n) (m_len p0 pl p n) text copy arr (m_D p0 pl p n)
      (Mem.le8 (Z_to_bv 64 (n - hdr_n n))))
    (MS (Regs6ss.mkR_of regs) (@fp_regs fx) (Z_to_bv 64 0x14200) (@fp_csr fx) None (normalize_cj rsegs mem)
       (seg_rom rsegs)).
Proof.
  intros CRC CAC MEMC SSPN SCSPN fx L A regs mem md O R1 x quit text copy arr jw m p n R0
    (HCF & HRC & EVR & HRX & D1 & D2 & D3 & T16 & C16 & A16 & HLR & G10 & G18 & G19 & G20 & G21 & LC0 & LC1 & MP & _).
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & R2 & R3 & R4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HRX as (REP & SPILL & QB & Hq & ENO & BLK & XC & HOL).
  pose proof HLR as (L8 & L9 & L23 & L22 & L26 & L24 & L25 & L27 & Hm & Hn & Hp & Hpn).
  assert (SEGS : ms_segs B = rsegs) by exact (it_SEGS B API LS SH SK ra empty FG).
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  assert (TS : S <= TASK_SIZE) by (eapply it_TS; eassumption).
  assert (S16 : S mod 16 = 0) by (eapply it_S16; eassumption).
  pose proof (q3h_m8 _ T16) as T8. pose proof (q3h_m8 _ C16) as C8'. pose proof (q3h_m8 _ A16) as A8.
  assert (LO8 : (S - SLOT_STACK) mod 8 = 0) by (unfold SLOT_STACK; clear - S16; Z.div_mod_to_equations; lia).
  clear T16 C16 A16.
  pose proof alloc_ceiling_val as AC.
  assert (Hn0 : 0 < n0) by (clear - Hn Hp Hpn; lia).
  destruct (it_inblk B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A regs mem md HCF Hn0)
    as (IB & IB0 & Hp04 & Hpac & HL & _).
  pose proof (m_len_range p0 pl p n Hn) as [HL1 HL2].
  pose proof (m_D_len p0 n0 pl p n Hn Hp Hpn HL) as HDL.
  pose proof (SlotRec.strnlen_upto0 _ _ HDL) as HU.
  set (LWv := strnlen_res (m_len p0 pl p n) (m_D p0 pl p n)) in *.
  assert (LWR : 0 <= LWv <= m_len p0 pl p n).
  { assert (E : Verbs.upto0 (m_D p0 pl p n) = firstn (length (Verbs.upto0 (m_D p0 pl p n))) (m_D p0 pl p n))
      by (unfold Verbs.upto0; apply SlotWords.sw_upto_prefix).
    apply (f_equal (@length byte)) in E. rewrite length_firstn in E. clear - E HU HDL. lia. }
  destruct (XC _ (or_introl eq_refl)) as (XT & NT0 & NTO).
  destruct (XC _ (or_intror (or_introl eq_refl))) as (XCo & NC0 & NCO).
  destruct (XC _ (or_intror (or_intror (or_introl eq_refl)))) as (XA & NA0 & NAO).
  cbn [fst] in NTO, NCO, NAO.
  assert (ASZ : 16 <= arr_size LWv <= 2 ^ 16) by (unfold arr_size; clear - LWR HL1; Z.div_mod_to_equations; lia).
  destruct (q3h_blk B API LS SH SK ra empty FG fx L A mem md text (LWv + 1) M XT ltac:(clear - LWR; lia))
    as (TB1 & TB2 & TB3).
  destruct (q3h_blk B API LS SH SK ra empty FG fx L A mem md copy (LWv + 1) M XCo ltac:(clear - LWR; lia))
    as (CB1 & CB2 & CB3).
  destruct (q3h_blk B API LS SH SK ra empty FG fx L A mem md arr (arr_size LWv) M XA ltac:(clear - ASZ; lia))
    as (AB1 & AB2 & AB3).
  assert (DTC := q3h_disj B API fx L A mem md _ _ _ _ M XT XCo ltac:(intros E; exact (D1 (f_equal fst E)))).
  assert (DTA := q3h_disj B API fx L A mem md _ _ _ _ M XT XA ltac:(intros E; exact (D2 (f_equal fst E)))).
  assert (DCA := q3h_disj B API fx L A mem md _ _ _ _ M XCo XA ltac:(intros E; exact (D3 (f_equal fst E)))).
  assert (DIT := q3h_disj B API fx L A mem md p0 n0 text _ M IB XT
    ltac:(intros E; rewrite E in IB0; exact (NT0 IB0))).
  assert (USP : bv_unsigned (Z_to_bv 64 FB) = FB).
  { apply unsigned_lit. unfold SlotInv.FB. unfold SLOT_STACK in HS. clear - HS AC. lia. }
  (* the premises of q3_evt *)
  assert (H_lo : 0x54f98 <= S - SLOT_STACK) by (unfold SLOT_STACK in *; clear - HS AC; lia).
  assert (H_LOS : S - SLOT_STACK + 6000 <= bv_unsigned (Z_to_bv 64 FB))
    by (rewrite USP; unfold SlotInv.FB, SLOT_STACK; clear - HS; lia).
  assert (H_SPH : bv_unsigned (Z_to_bv 64 FB) + 160 <= 2 ^ 63) by (rewrite USP; unfold SlotInv.FB; clear - HS; lia).
  assert (H_TS : bv_unsigned (Z_to_bv 64 FB) + 160 <= TASK_SIZE) by (rewrite USP; unfold SlotInv.FB; clear - TS; lia).
  assert (H_SP8 : bv_unsigned (Z_to_bv 64 FB) mod 8 = 0)
    by (rewrite USP; unfold SlotInv.FB; clear - S16; Z.div_mod_to_equations; lia).
  assert (H_len : 0 <= m_len p0 pl p n <= 8192) by (clear - HL1; lia).
  assert (H_src : 0 <= m_src p n /\ m_src p n + m_len p0 pl p n <= S - SLOT_STACK).
  { unfold m_src, hdr_n in *. unfold SLOT_STACK in *. clear - HL1 HL2 Hp Hpn Hp04 Hpac HS Hn. lia. }
  assert (H_L0 : 0 <= LWv <= m_len p0 pl p n) by exact LWR.
  assert (H_tx : 0 < text /\ text + LWv + 1 <= S - SLOT_STACK) by (unfold SLOT_STACK in *; clear - TB1 TB2 HS; lia).
  assert (H_cp : 0 < copy /\ copy + LWv + 1 <= S - SLOT_STACK) by (unfold SLOT_STACK in *; clear - CB1 CB2 HS; lia).
  assert (H_ar : 0 < arr /\ arr + arr_size LWv <= S - SLOT_STACK) by (unfold SLOT_STACK in *; clear - AB1 AB2 HS; lia).
  assert (H_AS : arr_size LWv = 8 * (LWv / 2) + 16) by reflexivity.
  assert (H_txi : text + LWv + 1 <= 0x10000 \/ 0x54f98 <= text) by (clear - TB3; lia).
  assert (H_cpi : copy + LWv + 1 <= 0x10000 \/ 0x54f98 <= copy) by (clear - CB3; lia).
  assert (H_ari : arr + arr_size LWv <= 0x10000 \/ 0x54f98 <= arr) by (clear - AB3; lia).
  assert (H_d1 : text + LWv + 1 <= copy \/ copy + LWv + 1 <= text) by (clear - DTC; lia).
  assert (H_d2 : arr + arr_size LWv <= text \/ text + LWv + 1 <= arr) by (clear - DTA; lia).
  assert (H_d3 : arr + arr_size LWv <= copy \/ copy + LWv + 1 <= arr) by (clear - DCA; lia).
  assert (H_d4 : m_src p n + m_len p0 pl p n <= text \/ text + LWv + 1 <= m_src p n).
  { unfold m_src, hdr_n in *. clear - DIT HL1 HL2 Hp Hpn Hn. lia. }
  assert (H_al : text mod 8 = 0 /\ arr mod 8 = 0 /\ (S - SLOT_STACK) mod 8 = 0) by (split; [|split]; assumption).
  pose proof (MemNorm.mem_inv_cj_task rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)) as H_tk.
  destruct (it_vrt B API LS SH SK ra empty FG fx L A mem md M GIm) as (can0 & _ & _ & V3 & V4).
  assert (SSPn : VerbsMem.ssp_at (normalize_cj rsegs mem) can0).
  { unfold VerbsB.SSP_GOT_B, VerbsB.SSP_GUARD_B in V3, V4. unfold VerbsMem.ssp_at, VerbsMem.SSP_GOT, VerbsMem.SSP_GUARD.
    assert (G1' : bytes_at (ms_segs B) mem 142656 (Mem.le8 (Z_to_bv 64 345904)))
      by (apply (chain_words.cw_le_bytes B mem); [exact V3 | clear - V3; lia | clear - V3; rewrite Mem.length_le8; lia]).
    assert (G2' : bytes_at (ms_segs B) mem 345904 (Mem.le8 can0))
      by (apply (chain_words.cw_le_bytes B mem); [exact V4 | clear - V4; lia | clear - V4; rewrite Mem.length_le8; lia]).
    rewrite SEGS in G1', G2'.
    split.
    - apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [clear - RO; rewrite Mem.length_le8; unfold TASK_SIZE; lia | exact G1'].
    - apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [clear - RO; rewrite Mem.length_le8; unfold TASK_SIZE; lia | exact G2']. }
  destruct (chain_words.cw_f18 _ _ SSPn) as [H_gg (can & H_gu)].
  destruct (it_FA B API LS SH SK ra empty FG fx) as (_ & _ & _ & _ & _ & SLACK & _).
  assert (H_cs : forall a, copy + LWv + 1 <= a < 8 * ((copy + LWv + 1 + 7) / 8) ->
            mbyte rsegs (normalize_cj rsegs mem) a <> None).
  { intros a Ha.
    assert (Pa : present mem a).
    { apply (SLACK L A mem md copy (LWv + 1) a M XCo). rewrite Z.add_assoc. exact Ha. }
    assert (H8 : a < copy + LWv + 1 + 8) by (clear - Ha; Z.div_mod_to_equations; lia).
    pose proof (q3_ha1 copy LWv a (proj1 LWR) CB1 CB2 (proj1 Ha) H8) as Ha1.
    pose proof (q3_ha2 copy LWv a (proj1 LWR) CB3 Ha) as Ha2.
    rewrite (proj1 (q3h_cj_mbyte mem a Ha1 Ha2)).
    destruct Pa as [bb Eb]. unfold mbyte. rewrite Eb. discriminate. }
  assert (GI' : forall a, in_globals frame_RELRO a -> mbyte rsegs mem a = seg_rom rsegs (Z_to_bv 64 a)).
  { intros a Ha. rewrite <- SEGS. exact (GIm a Ha). }
  destruct (SlotRec.relro_img mem GI') as (IG1 & _ & _ & IG4 & IG5 & IG6 & _ & _).
  assert (H_grec : bytes_at rsegs (normalize_cj rsegs mem) GOT_GREC (le8 (Z_to_bv 64 G_REC))).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [q3_cz | exact IG1]. }
  assert (H_gq : bytes_at rsegs (normalize_cj rsegs mem) GOT_GQUIT (le8 (Z_to_bv 64 G_QUIT))).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [q3_cz | exact IG4]. }
  assert (H_sh : bytes_at rsegs (normalize_cj rsegs mem) G_SHAPES g_shapes_bytes).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [q3_cz | exact IG5]. }
  assert (H_par : bytes_at rsegs (normalize_cj rsegs mem) G_PARSED g_parsed_bytes).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [q3_cz | exact IG6]. }
  assert (H_q : 0 <= qv quit < 2 ^ 32 /\ bytes_at rsegs (normalize_cj rsegs mem) G_QUIT (le4 (Z_to_bv 64 (qv quit)))).
  { split; [exact Hq|]. apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [q3_cz | exact QB]. }
  (* the recorder *)
  assert (EVRp : OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_c.vr_run (rec_clear R0)
    (m_D p0 pl p n) = (R1, x, quit)) by exact EVR.
  pose proof MP as MP'. unfold msg_props in MP'. cbv zeta in MP'. rewrite EVRp in MP'. cbv beta iota in MP'.
  destruct MP' as (NR1 & RR & N0 & _ & AOK & ROK & ARO & _).
  destruct (it_rep_parts L A mem R1 O REP) as [_ (_ & _ & X3 & _ & _ & _)].
  rewrite NR1 in X3.
  assert (H_nr : bytes_at rsegs (normalize_cj rsegs mem) (G_REC + REC_NREPLIES) (le4 (Z_to_bv 64 1))).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [q3_cz | exact X3]. }
  assert (LOA : alloc_ceiling <= S - SLOT_STACK) by (clear - HS; lia).
  destruct (q3h_rep B API LS SH SK ra empty FG fx L A mem md R1 O text copy arr _ _ _ x (S - SLOT_STACK) M REP
              XT NTO XCo NCO XA NAO T8 C8' A8 LO8 LOA RR)
    as (rep & slack & RP0 & RS0 & H_rnz & RB0 & H_sl & ROUT).
  destruct (q3h_ans B API LS SH SK ra empty FG fx L A mem md R1 O text copy arr _ _ _ (S - SLOT_STACK) M REP
              XT NTO XCo NCO XA NAO LOA)
    as (ans & xa & AN0 & HAN & HAZ).
  destruct (q3h_calls L A mem R1 O REP) as (NC1 & NC2 & FN0).
  assert (H_rp : bytes_at rsegs (normalize_cj rsegs mem) (G_REC + REC_REPLY) (le8 rep)).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [rewrite length_le8; q3_cz | exact RP0]. }
  assert (H_rs : bytes_at rsegs (normalize_cj rsegs mem) (G_REC + REC_REPLY_SIZE)
                   (le8 (Z_to_bv 64 (Z.of_nat (length x) + 1)))).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [rewrite length_le8; q3_cz | exact RS0]. }
  assert (H_ans : bytes_at rsegs (normalize_cj rsegs mem) (G_REC + REC_ANSWER) (le8 ans)).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [rewrite length_le8; q3_cz | exact AN0]. }
  assert (H_rb : bytes_at rsegs (normalize_cj rsegs mem) (bv_unsigned rep) (x ++ NUL :: slack)).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [|exact RB0].
    rewrite length_app. cbn [length].
    pose proof (ROUT (Z.of_nat (length x) + Z.of_nat (length slack)) ltac:(clear - x slack; lia)) as (_ & _ & _ & H).
    unfold TASK_SIZE. clear - H HS TS. unfold SLOT_STACK in *. unfold TASK_SIZE in TS. lia. }
  assert (H_ro : forall i, 0 <= i < Z.of_nat (length x) + 1 + Z.of_nat (length slack) ->
            Frame.outside [(text, text + LWv + 1); (copy, copy + LWv + 1); (arr, arr + arr_size LWv);
                           (bv_unsigned (Z_to_bv 64 FB) - 96, bv_unsigned (Z_to_bv 64 FB) + 56)] (bv_unsigned rep + i) /\
            bv_unsigned rep + i < S - SLOT_STACK).
  { intros i Hi. destruct (ROUT i Hi) as (O1 & O2 & O3 & O4). split; [|exact O4].
    rewrite USP. apply q3h_out4; unfold SlotInv.FB, SLOT_STACK in *; clear - O1 O2 O3 O4; lia. }
  assert (H_ab : bv_unsigned ans <> 0 -> cstr_at (normalize_cj rsegs mem) (bv_unsigned ans) xa /\
            forall i, 0 <= i < Z.of_nat (length xa) + 1 ->
              Frame.outside [(text, text + LWv + 1); (copy, copy + LWv + 1); (arr, arr + arr_size LWv);
                             (bv_unsigned (Z_to_bv 64 FB) - 96, bv_unsigned (Z_to_bv 64 FB) + 56)] (bv_unsigned ans + i) /\
              bv_unsigned ans + i < S - SLOT_STACK).
  { intros Hne. destruct (HAN Hne) as (_ & [Hb Hn'] & AOUT). split; [split; [|exact Hn']|].
    - apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [|exact Hb].
      rewrite length_app. cbn [length].
      pose proof (AOUT (Z.of_nat (length xa)) ltac:(clear - xa; lia)) as (_ & _ & _ & H).
      clear - H HS TS. unfold SLOT_STACK in *. unfold TASK_SIZE in *. lia.
    - intros i Hi. destruct (AOUT i Hi) as (O1 & O2 & O3 & O4). split; [|exact O4].
      rewrite USP. apply q3h_out4; unfold SlotInv.FB, SLOT_STACK in *; clear - O1 O2 O3 O4; lia. }
  assert (H_aok : U.Prog.check_reply_answer_c.answer_ok ans x xa
                    (Z.of_nat (length (Verbs.words (Verbs.line (m_D p0 pl p n)))))
                    (nth 0 (Verbs.words (Verbs.line (m_D p0 pl p n))) [])).
  { split.
    - intros Hne. destruct (HAN Hne) as (EA & _). rewrite EA in AOK. exact AOK.
    - intros Hz. rewrite (HAZ Hz) in AOK. exact AOK. }
  assert (H_nc : 0 <= Z.of_nat (length (r_calls R1)) <= 16 /\
            bytes_at rsegs (normalize_cj rsegs mem) (G_REC + REC_NCALLS)
              (le4 (Z_to_bv 64 (Z.of_nat (length (r_calls R1)))))).
  { split; [exact NC1|]. apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [q3_cz | exact NC2]. }
  assert (H_fn : 0 < Z.of_nat (length (r_calls R1)) -> 0 <= fst (nth 0 (r_calls R1) (0, [])) < 26 /\
            bytes_at rsegs (normalize_cj rsegs mem) (G_REC + REC_CALLS + CALL_FN)
              (le4 (Z_to_bv 64 (fst (nth 0 (r_calls R1) (0, [])))))).
  { intros Hp'. destruct (FN0 Hp') as [F1 F2]. split; [exact F1|].
    apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [q3_cz | exact F2]. }
  (* the run's own premises *)
  pose proof (MemNorm.mem_inv_cj_inv rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)) as MI.
  assert (ST : stk rsegs (normalize_cj rsegs mem) (S - SLOT_STACK) (bv_unsigned (Z_to_bv 64 FB))).
  { rewrite USP. apply RecAns.stk_normalize_cj;
      [unfold SLOT_STACK in *; clear - HS AC; lia | unfold SlotInv.FB; clear - TS; lia|].
    intros a Ha. apply SW. left. rewrite RG2. unfold SlotInv.FB in Ha. clear - Ha. lia. }
  assert (HSRC : 0 <= m_src p n - p0) by (unfold m_src, hdr_n; clear - Hp Hn; lia).
  pose proof (it_in_bytes B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A regs mem md HCF Hn0
     (m_src p n - p0) (m_len p0 pl p n) HSRC ltac:(clear - HL1; lia)
     ltac:(unfold m_src, hdr_n in *; clear - HL1 HL2 Hp Hpn Hn; lia)) as HD.
  replace (p0 + (m_src p n - p0)) with (m_src p n) in HD by ring.
  change (firstn (Z.to_nat (m_len p0 pl p n)) (skipn (Z.to_nat (m_src p n - p0)) pl)) with (m_D p0 pl p n) in HD.
  assert (SRC : bytes_at rsegs (normalize_cj rsegs mem) (m_src p n) (m_D p0 pl p n)).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [|exact HD].
    rewrite HDL. destruct H_src as [_ Hs2]. unfold SLOT_STACK in *. clear - Hs2 HS TS. lia. }
  destruct (q3h_u8 B API LS SH SK ra empty FG fx L A mem md text (LWv + 1) M XT ltac:(clear - LWR; lia))
    as (jt & TX & LT).
  destruct (q3h_u8 B API LS SH SK ra empty FG fx L A mem md copy (LWv + 1) M XCo ltac:(clear - LWR; lia))
    as (jc & CP & LC).
  destruct (q3h_u8 B API LS SH SK ra empty FG fx L A mem md arr (arr_size LWv) M XA ltac:(clear - ASZ; lia))
    as (ja & AR & LA).
  assert (FR0 : rw_cells rsegs (normalize_cj rsegs mem) (bv_unsigned (Z_to_bv 64 FB))
                  (LOC0 (le8 (Z_to_bv 64 (n - hdr_n n))))).
  { rewrite USP. apply q3_loc1_loc0.
    apply q3h_cj_cells; [exact LC0 | unfold SlotInv.FB, SLOT_STACK in *; clear - HS AC; lia | | ].
    - unfold LOC1. cbn. unfold SlotInv.FB, TASK_SIZE in *. clear - TS. lia.
    - intros i Hi. unfold LOC1 in Hi. cbn in Hi. unfold SlotInv.FB, SLOT_STACK in *. clear - Hi HS AC. lia. }
  assert (FR1 : rw_cells rsegs (normalize_cj rsegs mem) (bv_unsigned (Z_to_bv 64 FB) + 24)
                  [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); CB 16 jw]).
  { rewrite USP. apply q3h_cj_cells; [exact LC1 | unfold SlotInv.FB, SLOT_STACK in *; clear - HS AC; lia | | ].
    - cbn. unfold SlotInv.FB, TASK_SIZE in *. clear - TS. lia.
    - intros i Hi. cbn in Hi. unfold SlotInv.FB, SLOT_STACK in *. clear - Hi HS AC. lia. }
  unfold Regs6ss.mkR_of.
  assert (E2 : reg_get regs 2 = Z_to_bv 64 FB) by exact R2.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (m_src p n)) by exact L8.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 (m_len p0 pl p n)) by exact L9.
  assert (E10 : reg_get regs 10 = Z_to_bv 64 arr) by exact G10.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 LWv) by exact G20.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 MASK) by exact L24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 32) by exact L25.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (2 ^ 64 - 1)) by exact L27.
  rewrite E2, E8, E9, E10, E20, E24, E25, E27.
  subst LWv.
  exact (q3_evt (Z_to_bv 64 FB) (reg_get regs 3) (reg_get regs 4) (reg_get regs 18) (reg_get regs 19)
    (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 26) (@fp_regs fx) (@fp_csr fx)
    (normalize_cj rsegs mem) (S - SLOT_STACK) (m_src p n) (m_len p0 pl p n) text copy arr (m_D p0 pl p n)
    (le8 (Z_to_bv 64 (n - hdr_n n))) can
    H_lo H_LOS H_SPH H_TS H_SP8 H_len H_src H_L0 H_tx H_cp H_ar H_AS CRC CAC HDL H_txi H_cpi H_ari H_d1 H_d2 H_d3 H_d4
    H_al FZ H_tk H_gg H_gu H_cs
    ans rep x slack xa (Z.of_nat (length (r_calls R1))) (fst (nth 0 (r_calls R1) (0, []))) (qv quit)
    H_grec H_ans H_nr H_rp H_rs H_sh H_rnz H_rb N0 H_sl H_ro H_ab H_aok (SlotItHP.hp_reply_ok _ _ _ ROK) H_par H_nc H_fn
    H_gq H_q (SlotItHP.hp_arity_ok _ _ _ _ _ ARO)
    SSPN SCSPN MEMC
    (reg_get regs 1) (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 11) (reg_get regs 12)
    (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 28)
    (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)
    jt jc ja jw MI ST SRC TX LT CP LC AR LA FR0 FR1).
Qed.

(* seg_b2 inside the iteration section: stB to SR stBW. *)
Lemma q3_seg : check_reply_contract -> check_arity_contract -> U.Prog.memcpy_c.memcpy_contract ->
  U.Prog.strspn_c.strspn_contract -> U.Prog.strcspn_c.strcspn_contract ->
  forall (m p n : Z) (R0 : rstate) (c : config),
  stB B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c ->
  SR rsegs c (stBW B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0).
Proof.
  intros CRC CAC MEMC SSPN SCSPN m p n R0 c HB.
  destruct (q3h_stB B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c HB)
    as (fx & L & A & regs & mem & md & O & R1 & x & quit & text & copy & arr & jw & -> & HSB0).
  assert (HSB : SB B API S rg mem0 md0 L0 A0 p0 n0 pl fx L A regs mem md O R1 x quit text copy arr jw m p n R0)
    by exact HSB0.
  clear HSB0.
  pose proof HSB as (HCF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DCL & RS & RH).
  pose proof HCF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RO & _).
  destruct (it_model B API S rg mem0 md0 L0 A0 fx L A regs mem md HCF) as [Hh Hl].
  eapply (@sr_cj fx regs (Z_to_bv 64 0x14200) mem md _ _ Hh Hl RO).
  { exact (q3_evtS CRC CAC MEMC SSPN SCSPN fx L A regs mem md O R1 x quit text copy arr jw m p n R0 HSB). }
  { intros s0 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s4' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
      T & C & Aa & wp & jp & -> & _).
    do 5 eexists. reflexivity. }
  intros R' F' pc' fc' m0' regs' mem' HQ REL ROS GR.
  apply SR_ret.
  exact (@b3_post_u rc B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx L A regs mem md
    O R1 x quit text copy arr jw m p n R0 HSB DCL RS RH R' F' pc' fc' m0' regs' mem' HQ REL ROS GR).
Qed.

End Q3.

(* SlotItProof.seg_b2_spec. *)
Theorem seg_b2_q : seg_b2_spec.
Proof.
  unfold seg_b2_spec.
  intros B API LS SH SK ra empty rc S rg mem0 md0 L0 A0 p0 n0 pl b FG CC HP PRE RG2 m p n R0 c HB.
  destruct CC as (SMC & CWC & CRTC & RCC & CRPL & CAR & CRF & SNL & MEMC & SSP & SCSP).
  exact (@q3_seg rc B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 CRPL CAR MEMC SSP SCSP
    m p n R0 c HB).
Qed.
