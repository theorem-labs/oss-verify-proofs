(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan build of plugin-hostd/fuzz_command
   (0x89968, 135 instructions), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1.v..ACh8.v): the
   symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed by the shadow tokens
   (PaShadow.v), and the strcmp wrapper's call stepped through by its contract (PaArt.v aj_art_at). The two loops
   are cut at their heads (0x899dc, 0x89a6c) and at the outer latch (0x89ab0); each piece is re-seeded from the
   concrete state there and the loops are proved by induction. Every call is strcmp, which writes only its stack
   window, so the memory below the frame stays the entry's (kept_out) and the read-only bytes strcmp reads
   (rt_rom_view) follow from the statement's arodata_okP. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_equal.v, with its module paths, module names and numbers changed; 790 of its 1000 lines of code are new or changed and 1281 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of ieq on fuzz_segconf.asan-ubsan (image B, pin sha256 c3796c0b38f3,
   unstripped twin 80e82127e8ca; entry 0x87b70, 292 bytes, 73 instructions, a 48-byte frame, no side-stack frame):
   ieq_contract of lib/B/Prog/ieq_c.v at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre
   at the entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing
   lib/B/Prog/SegPa.v). Adapted from the image-A m_file-family lane's image-A walk lib/A/Prog/ieqA.v (commit
   056d4583918f: all 58 of A's instructions recur in order in B; B adds 15) and the segconf porter's UBSan walk
   lib/U/Prog/ieq.v (which fact kills each trap).

   The code (the neutral listing of ieq in image B):
     0x87b70-0x87ba0  frame of 48: ra s0 s1 s2 s3 at sp+40 .. sp+8; s0 := word, s1 := n, s3 := the shadow base
                      (the GOT word as_got_shadow B, image B 0xa3210 = listing A_OBJ 0, holds the cell
                      __asan_shadow_memory_dynamic_address 0xac7b8 = A_OBJ 12 that holds it), s2 := s, a0 := word;
                      0x87ba4 jal the strlen trampoline 0x43a98 (row 16, RtString.astrlen_realizes)
     0x87ba8          bne s1,a0 -> 0x87c68 (a0 := 0, the epilogue); 0x87bac a0 := 1; 0x87bb0 beqz s1 -> 0x87c6c
     0x87bb4-0x87bc8  a3 := (s <> 0), a4 := (word <> 0), a1 = a5 := s, a2 = a6 := word (s2 and s0 stay s and word)
     LOOP 0x87bcc     the UBSan pointer checks of s + i: bltu a1,s2 / a7 := a3 xor (a1 = 0), beqz a7 / beqz s2, each
                      to the trap 0x87c88 (unimp); the instrumented check of s[i] (a load of the shadow byte at
                      (a1 >> 3) + the shadow base and a compare; slow block 0x87c4c; the error path, a call of
                      errpath_load1 at 0x87c90, is not reached); the same three UBSan checks of word + i (0x87bf0
                      bltu a2,s0 / 0x87bfc beqz a7 / 0x87c00 beqz s0); the check of word[i] (slow block 0x87c58;
                      error path 0x87c64, not reached); lbu s[i] (a5), the fold b + 32 (b - 'A' <u 26) =
                      SegModel.lower b, lbu word[i] (a6), bne -> 0x87c68; s1 -= 1, the four cursors step,
                      beqz s1 -> 0x87c6c, j LOOP
     EPI 0x87c6c      ra s0 s1 s2 s3 restored, sp += 48, ret
   The six UBSan trap branches (each to the unimp at 0x87c88), each decided "not taken" by the symbolic executor
   at its branch (PaSym.v sym_step_pi: decide_cond2 under facts_ok, kit YP0e.v), from the loop head's facts
   (ie_l_facts below), so the trap instruction is never executed:
     0x87bcc bltu a1,s2   a1 = s + i, s2 = s: the assumed condition s + i >=u s (ie_l_conds; s + n <= alloc_ceiling
                          by the contract's sa_loc, so s + i does not wrap)
     0x87bd8 beqz a7      a7 = a3 xor (s + i = 0): a3 = 1 (s <> 0, the contract's premise; at byte 0 the
                          executor folds snez s to 1 from the entry fact s in [1, 2^64 - 1], ie_NZF) and
                          (s + i = 0) folds to 0 from the fact s + i in [4096, 2^47 - 64] (ie_PTRF), so a7 = 1
     0x87bdc beqz s2      s in [4096, 2^47 - 64] (ie_PTRF, atom 38; 4096 <= s from sa_loc)
     0x87bf0 bltu a2,s0   a2 = word + i, s0 = word: the assumed condition word + i >=u word (ie_l_conds)
     0x87bfc beqz a7      as 0x87bd8, from word <> 0 and word + i in [4096, 2^47 - 64]
     0x87c00 beqz s0      word in [4096, 2^47 - 64] (ie_PTRF, atom 39)
   Cut points (listing offsets from BASE = 0x84dc0): the entry AF_ieq 0x2db0; IE_LOOP 0x2e0c (0x87bcc) at byte i,
   re-seeded from the concrete state, the loop proved by induction on the bytes left; IE_EPI 0x2eac (0x87c6c),
   re-seeded with the saved registers. The two instrumented checks are decided by the shadow tokens (PaShadow.v)
   from one-byte shadow entries of s + i and word + i, whose range_addressable the contract's sa_addr gives.
   Memory: the code writes its own frame only and strlen its ESTACK window below it; every byte outside
   [sp - STK_ieq, sp) is kept (sa_kept), and s's and word's bytes lie below alloc_ceiling (sa_loc), so their facts
   hold at every point.
   Image numbers: the entry BASE + AF_ieq, the trampoline SIGMA SS___interceptor_trampoline_strlen (listing terms
   of lib/B/Prog/SegList.v / SegAddr.v); STK_ieq (= 48 + ESTACK: the frame of 48 and the ESTACK window row 16
   asks), RLO_A and RHI_A from lib/B/Prog/SegInstB.v (image B's values under SegInstA's names). The contract's
   argument `word` is named wd here: `word` is also the machine-word type these lemmas use. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import ieq_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module SM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegModel.
Module SP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.seg_spec.

(* image B: STK_ieq (SegInstB.v: frame 48 and strlen's ESTACK window) *)
#[local] Notation IE_STK := SegInstB.STK_ieq.

(* ---------- the model ---------- *)
Lemma ie_skipn_cons : forall {A} (l : list A) i d, (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof.
intros A l. induction l as [|x l IH]; intros [|i] d H; cbn [length] in H; try lia.
- reflexivity.
- cbn [skipn nth]. apply IH. lia.
Qed.
Lemma ie_skipn_all : forall {A} (l : list A) i, (length l <= i)%nat -> skipn i l = [].
Proof.
intros A l. induction l as [|x l IH]; intros [|i] H; cbn [length] in H; try lia; try reflexivity.
cbn [skipn]. apply IH. lia.
Qed.
Lemma ie_zs_length : forall bs, length (SP.zs bs) = length bs.
Proof. intros bs. unfold SP.zs. apply length_map. Qed.
Lemma ie_zb_length : forall l, length (SP.zb l) = length l.
Proof. intros l. unfold SP.zb. apply length_map. Qed.
Lemma ie_zs_nth : forall (l : list byte) i, (i < length l)%nat -> nth i (SP.zs l) 0 = bv_unsigned (nth i l ZB0).
Proof.
intros l i Hi. unfold SP.zs. rewrite (nth_indep _ 0 (bv_unsigned ZB0)) by (rewrite length_map; exact Hi).
apply map_nth.
Qed.
(* the word function of one byte value, checked on all 256 values *)
Lemma ie_zbrute : forall (F G : Z -> Z) c, 0 <= c < 256 ->
  forallb (fun k => F (Z.of_nat k) =? G (Z.of_nat k)) (seq 0 256) = true -> F c = G c.
Proof.
intros F G c Hc H. rewrite forallb_forall in H.
specialize (H (Z.to_nat c) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia. apply Z.eqb_eq. exact H.
Qed.
Ltac ie_brute c Hc :=
  lazymatch goal with |- ?L = ?R =>
    let F := lazymatch eval pattern c in L with ?F _ => F end in
    let G := lazymatch eval pattern c in R with ?G _ => G end in
    apply (ie_zbrute F G c Hc); vm_compute; reflexivity end.
Ltac ie_U_norm := repeat first [rewrite U_SAlu | rewrite U_SMd | rewrite U_SLit | rewrite U_SOff].
(* an assumed condition of the loop head: atom na >=u atom nb (the UBSan pointer checks; kit YI0m.v cond_geu's proof) *)
Lemma ie_cond_geu : forall E na nb a b, ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b ->
  0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> b <= a -> acond_ok E (mkAC BC_GEU (SOff na 0) (SOff nb 0)).
Proof.
intros E na nb a b Ha Hb Ra Rb Hle. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, (U_atom E na a Ha Ra), (U_atom E nb b Hb Rb).
apply negb_true_iff, Z.ltb_ge. exact Hle.
Qed.

(* ---------- bytes through a reader ---------- *)
Lemma ie_val1 : forall (rd : reader) a v, rd a = Some v -> 0 <= v < 256 -> sa_val rd a 1 v.
Proof.
intros rd a v H Hv k Hk. assert (k = 0%nat) by lia. subst k. change (Z.of_nat 0) with 0. rewrite Z.add_0_r, H. f_equal.
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a field read through the world's view is the same field of the restricted memory *)
Lemma ie_val_mem_of_sa_val : forall segs H mem a n v,
  sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
End r.

(* ---------- the symbolic states of the cut points ---------- *)
Definition IE_RET : Z := 0x2de8.   (* 0x87ba8, strlen's return *)
Definition IE_LOOP : Z := 0x2e0c.  (* 0x87bcc, the loop head (the first UBSan check, bltu a1,s2) *)
Definition IE_EPI : Z := 0x2eac.   (* 0x87c6c, the epilogue *)
(* the frame: ra s0 s1 s2 s3 saved at sp0-8 .. sp0-40 *)
Definition ie_saved : list Z := [1; 8; 9; 18; 19].
Definition ie_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition ie_SBF : afact := mkAF SB SB 0.
Definition ie_PTRF : afact := mkAF 4096 (2 ^ 47 - 64) 0.
Definition ie_CNTF : afact := mkAF 1 (2 ^ 63) 0.
Definition ie_BYTEF : afact := mkAF 0 255 0.
(* a nonzero word: s and word at the entry (the contract's s <> 0, word <> 0), so that snez s / snez word at
   0x87bb4 / 0x87bb8 fold to 1 *)
Definition ie_NZF : afact := mkAF 1 (2 ^ 64 - 1) 0.
Definition ie_Bx : sv := SOff 32 0.
(* the entry: atom 32 the shadow base; atoms 10 (s) and 12 (word) nonzero *)
Definition ie_ss_entry : sstate := mkSS AF_ieq sr_atoms [stack_region 48; got_regionP; bcell_regionP 32] None
  (mkFacts [(2%nat, ie_spF); (10%nat, ie_NZF); (12%nat, ie_NZF); (32%nat, ie_SBF)] [] []).
(* the epilogue: atoms 32..36 the saved ra, s0, s1, s2, s3 *)
Definition ie_estack : YP09.region := YP09.mkRegion (Some 2%nat) 0 48 0 0
  (map (fun j => YP09.mkChunk (40 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 5)).
Definition ie_ss_epi : sstate := mkSS IE_EPI sr_atoms [ie_estack] None (mkFacts [(2%nat, ie_spF)] [] []).
(* the loop head at byte i: atoms 32 the shadow base, 33 s + i, 34 word + i, 35 n - i, 36 s[i], 37 word[i],
   38 s, 39 word. Registers: s0 = word, s1 = n - i, a0 = 1, a1 = a5 = s + i, a2 = a6 = word + i, a3 = a4 = 1,
   s2 = s, s3 = the shadow base *)
Definition ie_l_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
   8 (SOff 39 0)) 9 (SOff 35 0)) 10 (SLit 1)) 11 (SOff 33 0)) 12 (SOff 34 0)) 13 (SLit 1)) 14 (SLit 1))
   15 (SOff 33 0)) 16 (SOff 34 0)) 18 (SOff 38 0)) 19 (SOff 32 0).
Definition ie_rs : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition ie_rw : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))].
(* the UBSan pointer checks 0x87bcc bltu a1,s2 and 0x87bf0 bltu a2,s0: s + i and word + i do not wrap *)
Definition ie_l_conds : list acond := [mkAC BC_GEU (SOff 33 0) (SOff 38 0); mkAC BC_GEU (SOff 34 0) (SOff 39 0)].
Definition ie_l_facts : facts := mkFacts
  [(2%nat, ie_spF); (32%nat, ie_SBF); (33%nat, ie_PTRF); (34%nat, ie_PTRF); (35%nat, ie_CNTF);
   (36%nat, ie_BYTEF); (37%nat, ie_BYTEF); (38%nat, ie_PTRF); (39%nat, ie_PTRF)] ie_l_conds [].
(* the shadow entries of the two checks: the byte s + i and the byte word + i are addressable *)
Definition ie_l_SH : list shent := [mkSHE 33 0 1; mkSHE 34 0 1].
Definition ie_ss_loop : sstate := mkSS IE_LOOP ie_l_regs [ie_rs] None ie_l_facts.
(* swap the one byte region of a state *)
Definition ie_swap (r : YP09.region) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) [r] (ss_resv ss) (ss_facts ss).

Ltac ie_regs_ok EE eqs :=
  apply regs_ok_by_cases; intros rr Hrr; cbv [all_regs In] in Hrr;
  repeat (destruct Hrr as [<- | Hrr];
    [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a0 ?rr2) =>
        let v := eval vm_compute in (sr_get a0 rr2) in change (sr_get a0 rr2) with v end;
      cbn [sv_denot];
      first [ reflexivity
            | rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply EE; reflexivity
            | rewrite ?Z.add_0_r; eqs; assumption
            | rewrite ?Z.add_0_r; eqs; unfold w64 in *; assumption ]
    | ]); try (destruct Hrr).
Ltac ie_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m | _ => idtac end end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Lemma ie_swap_ok : forall E ss ms r,
  st_ok_pi SEGS VAL E ss ms -> region_wf r = true -> region_ok SEGS E (ms_mem ms) r ->
  st_ok_pi SEGS VAL E (ie_swap r ss) ms.
Proof.
intros E ss ms r HS Hwf Hr.
pose proof (st_ok_pi_submem E ss ms [] HS (submem_nil _) eq_refl) as HS0.
pose proof (st_ok_pi_add_region E _ ms r HS0 Hwf Hr I) as HS1. exact HS1.
Qed.
(* a register the symbolic state holds as its own entry atom *)
Lemma ie_reg_atom : forall (H : word -> bool) Ex ss ms (r : bv 5) (k : nat) v,
  st_ok_pi SEGS VAL Ex ss (restrict H ms) -> Z.of_nat k = bv_unsigned r -> sr_get (ss_regs ss) r = SOff k 0 ->
  ew Ex k = v -> getr (ms_regs ms) r = v.
Proof.
intros H Ex ss ms r k v HS Hk Hr Hv. rewrite (st_ok_pi_restrict_reg H Ex ss ms r HS), Hr. cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hv.
Qed.

Ltac ie_same HS tac :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    apply (ie_reg_atom _ _ _ ms r k _ HS); [reflexivity | vm_compute; reflexivity | tac] end.
Section e.
Variable B : asyms.
(* the record hypothesis: PALib (lib/B/Prog/SegPaLib.v: the shadow GOT word A_OBJ 0 and the shadow cell A_OBJ 12 are
   as_got_shadow B and as_shadow_cell B, by role; image B 0xa3210 and 0xac7b8) *)
Hypothesis TL : PALib B.
(* the runtime entry the call reaches: the strlen wrapper at its trampoline (row 16; the image-B wrapper lane's image-B text
   lib/B/Rt/RtString.v; image B 0x43a98) *)
Hypothesis STRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Ltac ie_keep_empty HFr K lo hi :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end.
Ltac ie_keep_win HFr K lo hi Usp :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => lo <= x < hi) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]); destruct Hin
      | exact Hx0 | exact Hn0 ]) end.

(* the shadow entry of a range the walk's checks read *)
Lemma ie_shent_ok : forall E m n x lo hi, ew E 32 = w64 SB -> bv_unsigned (ew E n) = x -> 0 <= x + lo -> x + hi < 2 ^ 64 -> lo <= hi ->
  range_addressable (rd_of SEGS m) SHADOW_OFF (x + lo) (hi - lo) ->
  (forall y, x + lo <= y < x + hi -> ~ (SB <= y < SB + 2 ^ 44)) ->
  shent_ok SEGS ie_Bx E m (mkSHE n lo hi).
Proof.
intros E m n x lo hi H32 Hn H0 H1 Hlh Hra Hband. unfold shent_ok, app_apart, ie_Bx. cbn [she_m she_lo she_hi].
assert (U32 : U E (SOff 32 0) = SB).
{ rewrite U_SOff, H32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). apply zcanon_small. unfold SB; lia. }
assert (Hxr : 0 <= x < 2 ^ 64) by (rewrite <- Hn; pose proof (bv_unsigned_in_range 64 (ew E n)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR).
assert (Un : U E (SOff n 0) = x) by (rewrite U_SOff, Hn, Z.add_0_r; apply zcanon_small; exact Hxr).
rewrite U32, Un. split; [exact Hra|].
intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia. apply Hband. lia.
Qed.
(* the extra words of a seed *)
Lemma ie_ex_w64 : forall regs1 (l : list Z) j, (32 + j < A_TEXT)%nat -> (j < length l)%nat ->
  ew (Eimg (Ereg regs1 (map w64 l))) (32 + j) = w64 (nth j l 0).
Proof.
intros regs1 l j H1 H2. rewrite Eimg_low by exact H1. rewrite ew_Ereg_extra.
rewrite (nth_indep _ _ (w64 0)) by (rewrite length_map; exact H2). apply map_nth.
Qed.
(* where an object of segconf's code lies: a live heap block, a live side-stack frame or the image, below
   alloc_ceiling and apart from the shadow band *)
Lemma ie_loc : forall ly S W mem md q k, AR SEGS B ly S W mem md -> sa_loc SEGS B ly S q k -> 0 < k ->
  4096 <= q /\ q + k <= alloc_ceiling /\ (forall x, q <= x < q + k -> ~ (SB <= x < SB + 2 ^ 44)).
Proof.
intros ly S W mem md q k HAR HL Hk. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HL as [(b & m & Hin & Hb & Hbm) | [(cid & pos & Hin & Hc & Hf1 & Hf2) | Himg]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb4 & Hbc & Hba & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *.
  split; [lia|]. split; [lia|]. intros x Hx. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfa).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *.
  split; [lia|]. split; [lia|]. intros x Hx. lia.
- destruct (Himg q ltac:(lia)) as (Hi0 & _). destruct (Himg (q + k - 1) ltac:(lia)) as (Hi1 & _).
  pose proof (pa_img_range _ Hi0) as R0. pose proof (pa_img_range _ Hi1) as R1. unfold kImgEnd in R0, R1.
  split; [lia|]. split; [lia|]. intros x Hx. unfold SB. lia.
Qed.

(* ---------- one call of ieq ---------- *)
Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (s n wd : Z) (l : list byte) (w : list Z) (rlo rhi : Z).
Hypothesis HPRE : afn_pre SEGS B IE_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS rlo rhi B (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 s.
Hypothesis H11 : getr regs 11 = w64 n.
Hypothesis H12 : getr regs 12 = w64 wd.
(* s and word are nonzero words (the contract's ieq_pre and its range premises): the UBSan null checks *)
Hypothesis HS0 : s <> 0.
Hypothesis HW0 : wd <> 0.
Hypothesis Hs64 : 0 <= s < 2 ^ 64.
Hypothesis Hw64 : 0 <= wd < 2 ^ 64.
Hypothesis HSB : sa_bytes (rdW W mem) s l.
Hypothesis HLN : Z.of_nat (length l) = n.
Hypothesis HSA : sa_addr (rdW W mem) s n.
Hypothesis HSL : sa_loc SEGS B ly S s n.
Hypothesis HWS : sa_str (rdW W mem) wd w.
Hypothesis HWA : sa_addr (rdW W mem) wd (Z.of_nat (length w) + 1).
Hypothesis HWL : sa_loc SEGS B ly S wd (Z.of_nat (length w) + 1).
Hypothesis HW32 : Z.of_nat (length w) + 1 < 2 ^ 32.

Definition ie_RES : Z := SP.b2z (SM.ieq (SP.zs l) w).
Definition ie_Q : world SEGS -> config -> Prop :=
apost_base SEGS B IE_STK [] regs ly S W mem md EV_ieq
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (SP.b2z (SM.ieq (SP.zs l) w)) /\
 sa_kept SEGS W mem W' mem' regs IE_STK (fun _ => False) /\
 sa_noalloc B ly S ly' S').
(* the saved registers in the frame *)
Definition ie_frame (rd : reader) : Prop :=
forall j r, nth_error ie_saved j = Some r ->
sa_val rd (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* the callee-saved registers the code never writes *)
Definition ie_s4_11 (r1 : bvmap 5 word) : Prop :=
getr r1 20 = getr regs 20 /\ getr r1 21 = getr regs 21 /\ getr r1 22 = getr regs 22 /\ getr r1 23 = getr regs 23 /\
getr r1 24 = getr regs 24 /\ getr r1 25 = getr regs 25 /\ getr r1 26 = getr regs 26 /\ getr r1 27 = getr regs 27.
(* a cut point: the journal from the entry, every byte outside the stack window unchanged, the frame, sp, gp, tp
   and s4..s11 *)
Definition ie_cut (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal SEGS B IE_STK (spZ regs) [] ly S W mem md [] ly S W mem1 md1 0 /\
kept_out (rdW W mem) (rdW W mem1) (spZ regs - IE_STK) (spZ regs) /\
ie_frame (rdW W mem1) /\
getr regs1 2 = w64 (spZ regs - 48) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
ie_s4_11 regs1.

Lemma ie_sp : spZ regs mod 16 = 0 /\ alloc_ceiling + IE_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2). lia.
Qed.
Lemma ie_word_loc : 4096 <= wd /\ wd + Z.of_nat (length w) + 1 <= alloc_ceiling /\
  (forall x, wd <= x < wd + Z.of_nat (length w) + 1 -> ~ (SB <= x < SB + 2 ^ 44)).
Proof.
pose proof HPRE as (HAR & _).
destruct (ie_loc ly S W mem md wd _ HAR HWL ltac:(lia)) as (H1 & H2 & H3).
split; [exact H1|]. split; [lia|]. intros x Hx. apply H3. lia.
Qed.
Lemma ie_s_loc : 0 < n -> 4096 <= s /\ s + n <= alloc_ceiling /\ (forall x, s <= x < s + n -> ~ (SB <= x < SB + 2 ^ 44)).
Proof. intros Hn. pose proof HPRE as (HAR & _). exact (ie_loc ly S W mem md s n HAR HSL Hn). Qed.
Lemma ie_frame_kept : forall rd rd' lo hi, ie_frame rd -> kept_out rd rd' lo hi -> hi <= spZ regs - 48 ->
  ie_frame rd'.
Proof.
intros rd rd' lo hi HF HK Hhi j r Hr k Hk. pose proof ie_sp as (Hal16 & Hslo & Hshi).
pose proof asan_consts as (C1 & _). assert (HST : IE_STK = 4144) by reflexivity.
assert (Hj : (j < 5)%nat) by (change 5%nat with (length ie_saved); apply (proj1 (nth_error_Some ie_saved j)); rewrite Hr; discriminate).
rewrite (HK _) by lia. exact (HF j r Hr k Hk).
Qed.
(* a cut carried to a later state whose memory differs only in a window below the frame *)
Lemma ie_cut_kept : forall regs1 mem1 md1 regs2 mem2 md2 lo hi,
  ie_cut regs1 mem1 md1 ->
  ajournal SEGS B IE_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 ->
  kept_out (rdW W mem1) (rdW W mem2) lo hi -> spZ regs - IE_STK <= lo -> hi <= spZ regs - 48 ->
  getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
  getr regs2 20 = getr regs1 20 -> getr regs2 21 = getr regs1 21 -> getr regs2 22 = getr regs1 22 ->
  getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 -> getr regs2 25 = getr regs1 25 ->
  getr regs2 26 = getr regs1 26 -> getr regs2 27 = getr regs1 27 ->
  ie_cut regs2 mem2 md2.
Proof.
intros regs1 mem1 md1 regs2 mem2 md2 lo hi (HJ & HK & HFR & R2 & R3 & R4 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27)
  HJ2 HK2 Hlo Hhi Q2 Q3 Q4 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
pose proof ie_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact HJ2|]. split.
{ intros x Hx Hn. destruct (Z_lt_le_dec x lo) as [Hl|Hl]; [rewrite (HK2 x Hx) by lia; exact (HK x Hx Hn)|].
  destruct (Z_lt_le_dec x hi) as [Hh|Hh]; [exfalso; apply Hn; lia|]. rewrite (HK2 x Hx) by lia. exact (HK x Hx Hn). }
split; [exact (ie_frame_kept _ _ lo hi HFR HK2 Hhi)|].
rewrite Q2, Q3, Q4. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
unfold ie_s4_11. rewrite Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27. auto 10.
Qed.

(* ---------- the epilogue: 0x87c6c .. 0x87c84, ra s0 s1 s2 s3 restored, ret ---------- *)
Definition ie_e_extra : list word := map (fun r => getr regs (Z_to_bv 5 r)) ie_saved.
Lemma ie_e_nth : forall j r, nth_error ie_saved j = Some r -> nth j ie_e_extra (Z_to_bv 64 0) = getr regs (Z_to_bv 5 r).
Proof.
intros j r H. unfold ie_e_extra. apply nth_error_nth. rewrite (map_nth_error (fun r0 => getr regs (Z_to_bv 5 r0)) j ie_saved H). reflexivity.
Qed.
Lemma ie_epi_seed : forall regs1 mem1, getr regs1 2 = w64 (spZ regs - 48) -> ie_frame (rdW W mem1) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 ie_e_extra)) ie_ss_epi
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + IE_EPI)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS ie_Bx [] (Eimg (Ereg regs1 ie_e_extra)) (mrestrict (w_H W) mem1).
Proof.
intros regs1 mem1 R2 HFR. pose proof ie_sp as (Hal16 & Hlo & Hhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : IE_STK = 4144) by reflexivity.
set (E := Eimg (Ereg regs1 ie_e_extra)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 48).
{ subst E. rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold ie_ss_epi. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ie_estack.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
  destruct (nth_error ie_saved j) as [r|] eqn:Hr; [| apply nth_error_None in Hr; cbn in Hr; lia].
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
  apply (chunk_ok_val SEGS E _ (spZ regs - 48) (40 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra, (ie_e_nth j r Hr).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HRr.
  + cbn. lia.
  + replace (spZ regs - 48 + (40 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
    apply ie_val_mem_of_sa_val. exact (HFR j r Hr).
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, ie_spF. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.
Lemma ie_epi : forall regs1 mem1 md1, ie_cut regs1 mem1 md1 -> getr regs1 10 = w64 ie_RES ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + IE_EPI)) mem1 (seg_rom SEGS)) md1) ie_Q.
Proof.
intros regs1 mem1 md1 (HJ & HK & HFR & R2 & R3 & R4 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27) R10.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof ie_sp as (Hal16 & Hlo & Hhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : IE_STK = 4144) by reflexivity.
destruct (ie_epi_seed regs1 mem1 R2 HFR) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 ie_e_extra))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 ie_e_extra)) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j r, nth_error ie_saved j = Some r -> ew (Eimg (Ereg regs1 ie_e_extra)) (32 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hr. assert (Hj : (j < 5)%nat) by (change 5%nat with (length ie_saved); apply (proj1 (nth_error_Some ie_saved j)); rewrite Hr; discriminate).
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (ie_e_nth j r Hr). }
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs1 ie_e_extra)) 2) = spZ regs - 48).
{ rewrite (EE 2%nat 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
pose proof (EX 0%nat 1 eq_refl) as E32. pose proof (EX 1%nat 8 eq_refl) as E33. pose proof (EX 2%nat 9 eq_refl) as E34.
pose proof (EX 3%nat 18 eq_refl) as E35. pose proof (EX 4%nat 19 eq_refl) as E36.
cbn [Nat.add] in E32, E33, E34, E35, E36.
pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4. pose proof (EE 10%nat 10%bv eq_refl) as E10.
pose proof (EE 20%nat 20%bv eq_refl) as E20. pose proof (EE 21%nat 21%bv eq_refl) as E21.
pose proof (EE 22%nat 22%bv eq_refl) as E22. pose proof (EE 23%nat 23%bv eq_refl) as E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. pose proof (EE 25%nat 25%bv eq_refl) as E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. pose proof (EE 27%nat 27%bv eq_refl) as E27.
clear EX.
remember (Eimg (Ereg regs1 ie_e_extra)) as E eqn:HE0. clear HE0.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
ie_md.
ie_keep_empty HFr KEEPe (spZ regs - IE_STK) (spZ regs - IE_STK).
prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ie_Q, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split.
{ rewrite F1, E32. change (getr regs (Z_to_bv 5 1)) with (getr regs 1). unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| subst r];
  rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot];
  first
  [ rewrite Usp; replace (spZ regs - 48 + 48) with (spZ regs) by lia; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
  | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    first [ rewrite E3, R3; reflexivity | rewrite E4, R4; reflexivity
          | rewrite E20, R20; reflexivity | rewrite E21, R21; reflexivity | rewrite E22, R22; reflexivity
          | rewrite E23, R23; reflexivity | rewrite E24, R24; reflexivity | rewrite E25, R25; reflexivity
          | rewrite E26, R26; reflexivity | rewrite E27, R27; reflexivity
          | rewrite E33; reflexivity | rewrite E34; reflexivity | rewrite E35; reflexivity | rewrite E36; reflexivity ] ]. }
split; [|split].
- rewrite F10, E10. exact R10.
- intros a Ha Hn _. rewrite (KEEPe a Ha) by lia. exact (HK a Ha Hn).
- unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). destruct S; reflexivity.
Qed.

(* ---------- the facts of s and wd at a state whose memory agrees with the entry's below the window ---------- *)
Lemma ie_rom_at : forall memc, kept_out (rdW W mem) (rdW W memc) (spZ regs - IE_STK) (spZ regs) ->
  rt_rom_view SEGS B W memc.
Proof.
intros memc HK x Hx Ho He. pose proof ie_sp as (Hal16 & Hslo & Hshi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : IE_STK = 4144) by reflexivity.
destruct Hx as (sg & Hsg & Hw & Hr).
assert (Himg : in_img SEGS x) by (exists sg; split; [exact Hsg | exact Hr]).
pose proof (pa_img_range _ Himg) as HR. unfold kImgEnd in HR. rewrite (HK x) by lia.
apply HROD; [left; exists sg; split; [exact Hsg | split; [exact Hw | exact Hr]] | exact Ho | exact He].
Qed.
(* what the strlen wrapper asks of wd, at the call *)
Lemma ie_word_call : forall memc regsc,
  kept_out (rdW W mem) (rdW W memc) (spZ regs - IE_STK) (spZ regs) -> spZ regs - IE_STK <= spZ regsc - ESTACK ->
  astr_at SEGS W memc wd (SP.zb w) /\ aread_ok SEGS ESTACK W regsc memc wd (astr_len (SP.zb w) + 1) /\
  atail_vis SEGS W memc (wd + astr_len (SP.zb w)) /\ rt_rom_view SEGS B W memc.
Proof.
intros memc regsc HK Hsc.
pose proof ie_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : IE_STK = 4144) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof alloc_ceiling_value as [_ HAC].
destruct ie_word_loc as (Hw4 & Hwc & Hwb).
destruct HWS as [HZ HT].
destruct (sa_strz_bytes SEGS (w_H W) mem wd w HZ) as (HBy & HN & _). pose proof (ie_zb_length w) as HL.
unfold astr_len. rewrite HL.
split.
{ split; [|exact HN]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite HL in Hi.
  rewrite (HK (wd + Z.of_nat i)) by lia. exact (HBy i ltac:(rewrite length_app; cbn [length]; rewrite HL; lia)). }
split.
{ apply (aread_ok_kept SEGS ESTACK ESTACK W regs regsc mem memc (spZ regs - IE_STK) (spZ regs) wd _ HK);
    [| lia | unfold kHighShadowEnd; lia | lia | lia | lia].
  destruct HWA as (A0 & A1 & A2 & A3 & A4).
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
  intros a Ha. split; [|unfold ascratch_stk; lia].
  replace a with (wd + Z.of_nat (Z.to_nat (a - wd))) by lia.
  rewrite (HBy (Z.to_nat (a - wd))) by (rewrite length_app; cbn [length]; rewrite HL; lia).
  discriminate. }
split.
{ assert (Hxe : 0 <= wd + Z.of_nat (length w) < alloc_ceiling) by lia.
  pose proof (tail_below _ _ Hxe HAC) as HTB0.
  apply (atail_vis_kept SEGS W mem memc (spZ regs - IE_STK) (spZ regs) _ HK); [| lia | lia | lia].
  intros a Ha. exact (HT a Ha). }
exact (ie_rom_at memc HK).
Qed.

(* ---------- the loop head: 0x87bcc at byte i ---------- *)
Definition ie_l_extra (i : nat) (c x : Z) : list word :=
map w64 [SB; s + Z.of_nat i; wd + Z.of_nat i; n - Z.of_nat i; c; x; s; wd].
Definition ie_LP (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ie_cut regs1 mem1 md1 /\ Z.of_nat i < n /\ Z.of_nat (length w) = n /\
getr regs1 8 = w64 wd /\ getr regs1 9 = w64 (n - Z.of_nat i) /\ getr regs1 10 = w64 1 /\
getr regs1 11 = w64 (s + Z.of_nat i) /\ getr regs1 12 = w64 (wd + Z.of_nat i) /\
getr regs1 13 = w64 1 /\ getr regs1 14 = w64 1 /\
getr regs1 15 = w64 (s + Z.of_nat i) /\ getr regs1 16 = w64 (wd + Z.of_nat i) /\
getr regs1 18 = w64 s /\ getr regs1 19 = w64 SB /\
SM.ieq (SP.zs l) w = SM.ieq_go (skipn i (SP.zs l)) (skipn i w).
Lemma ie_loop_seed : forall (i : nat) c x regs1 mem1, Z.of_nat i < n -> 0 <= c < 256 -> 0 <= x < 256 ->
  getr regs1 2 = w64 (spZ regs - 48) ->
  getr regs1 8 = w64 wd -> getr regs1 9 = w64 (n - Z.of_nat i) -> getr regs1 10 = w64 1 ->
  getr regs1 11 = w64 (s + Z.of_nat i) -> getr regs1 12 = w64 (wd + Z.of_nat i) ->
  getr regs1 13 = w64 1 -> getr regs1 14 = w64 1 ->
  getr regs1 15 = w64 (s + Z.of_nat i) -> getr regs1 16 = w64 (wd + Z.of_nat i) ->
  getr regs1 18 = w64 s -> getr regs1 19 = w64 SB ->
  rdW W mem1 (s + Z.of_nat i) = Some c ->
  range_addressable (rdW W mem1) SHADOW_OFF (s + Z.of_nat i) 1 ->
  range_addressable (rdW W mem1) SHADOW_OFF (wd + Z.of_nat i) 1 ->
  Z.of_nat (length w) = n ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 (ie_l_extra i c x))) ie_ss_loop
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + IE_LOOP)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS ie_Bx ie_l_SH (Eimg (Ereg regs1 (ie_l_extra i c x))) (mrestrict (w_H W) mem1).
Proof.
intros i c x regs1 mem1 Hi Hc Hx R2 R8 R9 R10 R11 R12 R13 R14 R15 R16 R18 R19 VS RAS RAW HLW.
pose proof ie_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSA as (SA0 & SA1 & _).
assert (HST : IE_STK = 4144) by reflexivity.
destruct (ie_s_loc ltac:(lia)) as (Hs4 & Hsc & Hsb). destruct ie_word_loc as (Hw4 & Hwc & Hwb).
set (E := Eimg (Ereg regs1 (ie_l_extra i c x))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 48) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (EX : forall j v, nth_error [SB; s + Z.of_nat i; wd + Z.of_nat i; n - Z.of_nat i; c; x; s; wd] j = Some v ->
  ew E (32 + j) = w64 v).
{ intros j v Hj. assert (Hj8 : (j < 8)%nat) by (change 8%nat with (length [SB; s + Z.of_nat i; wd + Z.of_nat i; n - Z.of_nat i; c; x; s; wd]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  subst E. unfold ie_l_extra. rewrite ie_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 2%nat _ eq_refl) as E34.
pose proof (EX 3%nat _ eq_refl) as E35. pose proof (EX 4%nat _ eq_refl) as E36. pose proof (EX 5%nat _ eq_refl) as E37.
pose proof (EX 6%nat _ eq_refl) as E38. pose proof (EX 7%nat _ eq_refl) as E39.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39. clear EX.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = s + Z.of_nat i) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = wd + Z.of_nat i) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = n - Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = c) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = x) by (rewrite E37; apply unsigned_lit_small; lia).
assert (E38u : bv_unsigned (ew E 38) = s) by (rewrite E38; apply unsigned_lit_small; lia).
assert (E39u : bv_unsigned (ew E 39) = wd) by (rewrite E39; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ie_ss_loop. apply pa_entry_st_ok_full.
  + ie_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E34u, ?E35u, ?E36u, ?E37u, ?E38u, ?E39u).
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ie_rs.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E33u.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (s + Z.of_nat i) 0 1 (SOff 36 0) c); [cbn [sv_denot]; rewrite E36u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    apply ie_val_mem_of_sa_val. rewrite Z.add_0_r. exact (ie_val1 _ _ _ VS Hc).
  + cbn. tauto.
  + split; [|split; [|exact I]].
    * cbn [f_atoms atoms_ok ie_l_facts]. unfold afact_ok, ie_spF, ie_SBF, ie_PTRF, ie_CNTF, ie_BYTEF.
      cbn [af_lo af_hi af_al2].
      rewrite Usp, E32u, E33u, E34u, E35u, E36u, E37u, E38u, E39u. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
    * (* the two assumed conditions: s + i >=u s and word + i >=u word *)
      split; [|split; [|exact I]].
      { apply (ie_cond_geu E 33 38 (s + Z.of_nat i) s E33 E38); lia. }
      { apply (ie_cond_geu E 34 39 (wd + Z.of_nat i) wd E34 E39); lia. }
- unfold sh_ok, ie_l_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (ie_shent_ok E _ 33 (s + Z.of_nat i) 0 1 E32 E33u); try lia; [rewrite Z.add_0_r; exact RAS | intros y Hy; apply Hsb; lia].
  + apply (ie_shent_ok E _ 34 (wd + Z.of_nat i) 0 1 E32 E34u); try lia; [rewrite Z.add_0_r; exact RAW | intros y Hy; apply Hwb; lia].
Qed.

(* the fold b + 32 (b - 'A' <u 26) against word[i]: both sides of the bne at 0x87c2c, whichever side the executor
   puts first, rewritten to SegModel.lower s[i] and word[i] by checking the expression on all 256 byte values *)
Ltac ie_fold_rw Hc c Hcr x Hxr E36u E37u :=
  lazymatch type of Hc with context [U ?Ex ?A =? U ?Ex ?Bv] =>
    let UA := fresh "UA" in let UB := fresh "UB" in
    first
    [ assert (UA : U Ex A = SM.lower c) by (ie_U_norm; cbn [ew ewset Nat.eqb]; rewrite ?E36u, ?E37u; ie_brute c Hcr);
      assert (UB : U Ex Bv = x) by (ie_U_norm; cbn [ew ewset Nat.eqb]; rewrite ?E36u, ?E37u; ie_brute x Hxr)
    | assert (UA : U Ex Bv = SM.lower c) by (ie_U_norm; cbn [ew ewset Nat.eqb]; rewrite ?E36u, ?E37u; ie_brute c Hcr);
      assert (UB : U Ex A = x) by (ie_U_norm; cbn [ew ewset Nat.eqb]; rewrite ?E36u, ?E37u; ie_brute x Hxr) ];
    rewrite UA, UB in Hc; clear UA UB
  end.
(* ---------- one byte of the loop: 0x87bcc .. 0x87c48 ---------- *)
Lemma ie_loop_step : forall i regs1 mem1 md1,
  (Z.of_nat (Datatypes.S i) < n -> forall r m d, ie_LP (Datatypes.S i) r m d ->
    SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + IE_LOOP)) m (seg_rom SEGS)) d) ie_Q) ->
  ie_LP i regs1 mem1 md1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + IE_LOOP)) mem1 (seg_rom SEGS)) md1) ie_Q.
Proof.
intros i regs1 mem1 md1 NXT (HCUT & Hi & HLW & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R18 & R19 & HINV).
pose proof HSA as (SA0 & SA1 & _).
pose proof HCUT as (HJ & HK & HFR & R2 & R3 & R4 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof ie_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : IE_STK = 4144) by reflexivity.
destruct (ie_s_loc ltac:(lia)) as (Hs4 & Hsc & Hsb). destruct ie_word_loc as (Hw4 & Hwc & Hwb).
assert (Hil : (i < length l)%nat) by lia. assert (Hiw : (i < length w)%nat) by lia.
(* the two bytes and their shadow *)
set (c := bv_unsigned (nth i l ZB0)).
assert (VS : rdW W mem1 (s + Z.of_nat i) = Some c) by (rewrite (HK _) by lia; exact (HSB i Hil)).
set (x := nth i w 0).
assert (VW : rdW W mem1 (wd + Z.of_nat i) = Some x).
{ destruct HWS as [[HZ _] _]. rewrite (HK _) by lia.
  rewrite (HZ i ltac:(rewrite length_app; cbn [length]; lia)). rewrite app_nth1 by exact Hiw. reflexivity. }
pose proof (sa_aview_rng _ _ _ _ _ VS) as Hcr. pose proof (sa_aview_rng _ _ _ _ _ VW) as Hxr.
assert (RAS : range_addressable (rdW W mem1) SHADOW_OFF (s + Z.of_nat i) 1).
{ destruct HSA as (_ & _ & _ & A3 & _).
  apply (range_addressable_kept_win (rdW W mem) (rdW W mem1) (spZ regs - IE_STK) (spZ regs)); [exact HK | unfold kHighShadowEnd; lia | lia | lia |].
  apply (range_addressable_sub _ _ s n); [exact A3 | lia | lia]. }
assert (RAW : range_addressable (rdW W mem1) SHADOW_OFF (wd + Z.of_nat i) 1).
{ destruct HWA as (_ & _ & _ & A3 & _).
  apply (range_addressable_kept_win (rdW W mem) (rdW W mem1) (spZ regs - IE_STK) (spZ regs)); [exact HK | unfold kHighShadowEnd; lia | lia | lia |].
  apply (range_addressable_sub _ _ wd (Z.of_nat (length w) + 1)); [exact A3 | lia | lia]. }
(* the model at byte i *)
assert (HSK : skipn i (SP.zs l) = c :: skipn (Datatypes.S i) (SP.zs l)).
{ rewrite (ie_skipn_cons (SP.zs l) i 0) by (rewrite ie_zs_length; exact Hil). rewrite ie_zs_nth by exact Hil. reflexivity. }
assert (HWK : skipn i w = x :: skipn (Datatypes.S i) w) by (apply ie_skipn_cons; exact Hiw).
clearbody c x.
rewrite HSK, HWK in HINV. cbn [SM.ieq_go] in HINV.
destruct (ie_loop_seed i c x regs1 mem1 Hi Hcr Hxr R2 R8 R9 R10 R11 R12 R13 R14 R15 R16 R18 R19 VS RAS RAW HLW) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (ie_l_extra i c x)))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 (ie_l_extra i c x))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j v, nth_error [SB; s + Z.of_nat i; wd + Z.of_nat i; n - Z.of_nat i; c; x; s; wd] j = Some v ->
  ew (Eimg (Ereg regs1 (ie_l_extra i c x))) (32 + j) = w64 v).
{ intros j v Hj. assert (Hj8 : (j < 8)%nat) by (change 8%nat with (length [SB; s + Z.of_nat i; wd + Z.of_nat i; n - Z.of_nat i; c; x; s; wd]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  unfold ie_l_extra. rewrite ie_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 2%nat _ eq_refl) as E34.
pose proof (EX 3%nat _ eq_refl) as E35. pose proof (EX 4%nat _ eq_refl) as E36. pose proof (EX 5%nat _ eq_refl) as E37.
pose proof (EX 6%nat _ eq_refl) as E38. pose proof (EX 7%nat _ eq_refl) as E39.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39. clear EX.
remember (Eimg (Ereg regs1 (ie_l_extra i c x))) as E eqn:HE0. clear HE0.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 48) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = s + Z.of_nat i) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = wd + Z.of_nat i) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = n - Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = c) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = x) by (rewrite E37; apply unsigned_lit_small; lia).
(* 0x87bcc .. 0x87c18: the three UBSan checks of s + i (decided by ie_l_facts), the check of s[i] (slow block
   0x87c4c), the three UBSan checks of wd + i, the check of wd[i] (slow block 0x87c58), lbu s[i] (a5),
   t0 := s[i] - 65; lbu wd[i] (a6) at 0x87c1c needs wd + i's region *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
ie_md.
ie_keep_empty HFr KEEP1 (spZ regs - IE_STK) (spZ regs - IE_STK). clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?E2 _ (restrict _ ?msx) =>
  assert (RB : region_ok SEGS E2 (ms_mem (restrict (w_H W) msx)) ie_rw);
  [ cbn [ms_mem restrict]; unfold region_ok, ie_rw;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    cbn [ew ewset Nat.eqb]; rewrite E34u;
    split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val SEGS E2 _ (wd + Z.of_nat i) 0 1 (SOff 37 0) x);
    [cbn [sv_denot ew ewset Nat.eqb]; rewrite E37u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |];
    apply ie_val_mem_of_sa_val; rewrite Z.add_0_r; apply ie_val1; [rewrite (KEEP1 _) by lia; exact VW | exact Hxr]
  | ] end.
pose proof (ie_swap_ok _ _ _ ie_rw HS eq_refl RB) as HS'. clear HS RB. rename HS' into HS.
(* 0x87c1c .. 0x87c2c: lbu wd[i], the fold, bne a7,t1 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
ie_md.
ie_keep_empty HFr KEEP2 (spZ regs - IE_STK) (spZ regs - IE_STK). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the bytes differ: 0x87c68 a0 := 0, the epilogue *)
  assert (Hne : SM.lower c <> x).
  { rewrite branch_ne_U in Hc. ie_fold_rw Hc c Hcr x Hxr E36u E37u.
    apply negb_true_iff, Z.eqb_neq in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan IE_EPI.
  { awr_ok_tac. }
  ie_md.
  ie_keep_empty HFr KEEP3 (spZ regs - IE_STK) (spZ regs - IE_STK). clear HF HFr HG.
  pmkst HS.
  prreg HS (10%bv : bv 5) Q10.
  apply ie_epi.
  + lazymatch goal with |- ie_cut _ ?mF _ =>
      assert (KEEP : kept_out (rdW W mem1) (rdW W mF) (spZ regs - IE_STK) (spZ regs - IE_STK))
        by (apply (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia)) KEEP3); lia) end.
    apply (ie_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP); try lia;
      ie_same HS ltac:(cbn [ew ewset Nat.eqb]; apply EE; reflexivity).
  + rewrite Q10. unfold ie_RES. rewrite HINV. rewrite (proj2 (Z.eqb_neq _ _) Hne). reflexivity.
- (* the bytes agree: 0x87c30 .. 0x87c44, s1 -= 1, the four cursors step, beqz s1 *)
  assert (Heq : SM.lower c = x).
  { rewrite branch_ne_U in Hc. ie_fold_rw Hc c Hcr x Hxr E36u E37u.
    apply negb_false_iff, Z.eqb_eq in Hc. lia. }
  rewrite (proj2 (Z.eqb_eq _ _) Heq) in HINV. cbn [andb] in HINV.
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac. }
  ie_md.
  ie_keep_empty HFr KEEP3 (spZ regs - IE_STK) (spZ regs - IE_STK). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* the last byte: 0x87c6c with a0 = 1 *)
    assert (HiN : Z.of_nat i + 1 = n).
    { rewrite branch_eq_U in Hc. rewrite U_SLit in Hc.
      lazymatch type of Hc with (U ?Ex (SOff 35 ?o) =? _) = _ =>
        rewrite (U_atom_off Ex 35 (n - Z.of_nat i) o) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E35 | lia]) end.
      apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan IE_EPI.
    { awr_ok_tac. }
    ie_md.
    ie_keep_empty HFr KEEP4 (spZ regs - IE_STK) (spZ regs - IE_STK). clear HF HFr HG.
    pmkst HS.
    prreg HS (10%bv : bv 5) Q10.
    apply ie_epi.
    * lazymatch goal with |- ie_cut _ ?mF _ =>
        assert (KEEP : kept_out (rdW W mem1) (rdW W mF) (spZ regs - IE_STK) (spZ regs - IE_STK))
          by (apply (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _
                (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia)) KEEP3 ltac:(lia) ltac:(lia)) KEEP4); lia) end.
      apply (ie_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP); try lia;
        ie_same HS ltac:(cbn [ew ewset Nat.eqb]; apply EE; reflexivity).
    * rewrite Q10. unfold ie_RES. rewrite HINV.
      rewrite !ie_skipn_all by (first [rewrite ie_zs_length | idtac]; lia). reflexivity.
  + (* more bytes: 0x87c48 j 0x87bcc, the loop head at i + 1 *)
    assert (HiN : Z.of_nat (Datatypes.S i) < n).
    { rewrite branch_eq_U in Hc. rewrite U_SLit in Hc.
      lazymatch type of Hc with (U ?Ex (SOff 35 ?o) =? _) = _ =>
        rewrite (U_atom_off Ex 35 (n - Z.of_nat i) o) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E35 | lia]) end.
      apply Z.eqb_neq in Hc. change (zcanon 0) with 0 in Hc. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan IE_LOOP.
    { awr_ok_tac. }
    ie_md.
    ie_keep_empty HFr KEEP4 (spZ regs - IE_STK) (spZ regs - IE_STK). clear HF HFr HG.
    pmkst HS.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
    prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
    prreg HS (15%bv : bv 5) Q15. prreg HS (16%bv : bv 5) Q16. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
    apply (NXT HiN). split.
    { lazymatch goal with |- ie_cut _ ?mF _ =>
        assert (KEEP : kept_out (rdW W mem1) (rdW W mF) (spZ regs - IE_STK) (spZ regs - IE_STK))
          by (apply (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _
                (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia)) KEEP3 ltac:(lia) ltac:(lia)) KEEP4); lia) end.
      apply (ie_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP); try lia;
        ie_same HS ltac:(cbn [ew ewset Nat.eqb]; apply EE; reflexivity). }
    split; [exact HiN|]. split; [exact HLW|].
    split; [rewrite Q8, E39; reflexivity|].
    split; [rewrite Q9, E35u; unfold w64; f_equal; lia|].
    split; [rewrite Q10; reflexivity|].
    split; [rewrite Q11, E33u; unfold w64; f_equal; lia|].
    split; [rewrite Q12, E34u; unfold w64; f_equal; lia|].
    split; [rewrite Q13; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q15, E33u; unfold w64; f_equal; lia|].
    split; [rewrite Q16, E34u; unfold w64; f_equal; lia|].
    split; [rewrite Q18, E38; reflexivity|].
    split; [rewrite Q19, E32; reflexivity|].
    exact HINV.
Qed.
Lemma ie_loop_all : forall dd i, (i + dd = Z.to_nat n)%nat -> forall r m d, ie_LP i r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + IE_LOOP)) m (seg_rom SEGS)) d) ie_Q.
Proof.
induction dd as [|dd IH]; intros i Hd r m d HLP.
- exfalso. destruct HLP as (_ & Hi & _). lia.
- apply (ie_loop_step i); [|exact HLP].
  intros Hsi r' m' d' HLP'. apply (IH (Datatypes.S i)); [lia | exact HLP'].
Qed.

(* ---------- the entry: 0x87b70 .. 0x87bc8 ---------- *)
Lemma ie_stack_field : forall E H mem' cs off k v,
  region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 cs) -> bv_unsigned (ew E 2) = spZ regs ->
  In (YP09.mkChunk off (CVal 8 (SOff k 0))) cs -> ew E k = w64 v -> 0 <= v < 2 ^ 64 ->
  sa_val (aview SEGS H mem') (spZ regs + off) 8 v.
Proof.
intros E H mem' cs off k v HR Hsp Hin Hk Hv j Hj.
change 8%nat with (N.to_nat 8) in Hj |- *.
pose proof (field_of_region E _ 2 (spZ regs) cs (-48) 0 (-48) 0 off 8 (SOff k 0) v HR Hsp Hin) as HF.
assert (HFv : val_mem SEGS (mrestrict H mem') (spZ regs + off) (N.to_nat 8) v).
{ apply HF.
  - cbn [sv_denot]. rewrite Hk, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - cbn. lia. }
unfold aview. rewrite (HFv j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YG0f.le_byte. apply Z.mod_mod. lia.
Qed.
Lemma ie_entry_seed :
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 SB])) ie_ss_entry
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_ieq)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS ie_Bx [] (Eimg (Ereg regs [w64 SB])) (mrestrict (w_H W) mem).
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof ie_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : IE_STK = 4144) by reflexivity.
set (E := Eimg (Ereg regs [w64 SB])).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U10 : bv_unsigned (ew E 10) = s)
  by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 10 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = wd)
  by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 12 12%bv eq_refl), H12; unfold w64; apply unsigned_lit_small; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
assert (U241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite E241; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite E253; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pal_got_cell B TL) as HgcD.
unfold kImgEnd in HcellR, HgotR.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold ie_ss_entry. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
      | unfold SB; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- (* sp, s and word nonzero (for the folds of snez s / snez word at 0x87bb4 / 0x87bb8), the shadow base *)
  split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, ie_spF, ie_NZF, ie_SBF. cbn [af_lo af_hi af_al2].
  rewrite Usp, U10, U12, E32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). change (2 ^ 4) with 16.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; try lia; exact Hal16.
Qed.
Lemma ie_entry_gen :
  (forall r m d, ie_LP 0 r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + IE_LOOP)) m (seg_rom SEGS)) d) ie_Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_ieq) regs mem md) ie_Q.
Proof.
intros LOOP.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof ie_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : IE_STK = 4144) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct ie_word_loc as (Hw4 & Hwc & Hwb).
assert (Hnn : 0 <= n) by lia.
assert (Hn63 : n < 2 ^ 63) by (destruct HSA as (A0 & A1 & _); destruct (Z.eq_dec n 0); [lia|]; destruct (ie_s_loc ltac:(lia)) as (Hs4 & _); lia).
destruct ie_entry_seed as [HS SHOK].
pose proof (ajournal_init SEGS B IE_STK [] ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs [w64 SB]))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs [w64 SB])) k = getr regs r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew (Eimg (Ereg regs [w64 SB])) 32 = w64 SB) by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
remember (Eimg (Ereg regs [w64 SB])) as E eqn:HE0. clear HE0.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (FRM : forall H mem' cs, region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 cs) ->
  (forall j r, nth_error ie_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  ie_frame (aview SEGS H mem')).
{ intros H mem' cs HR Hin j r Hr.
  assert (Hr' : 1 <= r <= 19) by (apply nth_error_In in Hr; cbn in Hr; intuition lia).
  replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
  apply (ie_stack_field E H mem' cs _ (Z.to_nat r)); [exact HR | exact Usp | exact (Hin j r Hr) | |
    pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr; change (bv_modulus 64) with (2 ^ 64) in HRr; exact HRr].
  rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
unfold cfg_at. change (w64 (BASE + AF_ieq)) with (Z_to_bv 64 (BASE + AF_ieq)).
(* 0x87b70 .. 0x87ba4: the frame, s0 := wd, s1 := n, s3 := the shadow base, s2 := s, a0 := wd, jal strlen *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
ie_md.
ie_keep_win HFr KEEP0 (spZ regs - IE_STK) (spZ regs) Usp. clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
  pose proof (st_ok_region_nth (segs := SEGS) E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
  cbn [ms_mem restrict] in HRg end.
pose proof (FRM _ _ _ HRg) as FR0'.
specialize (FR0' ltac:(intros j r Hr; do 5 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]);
  cbn in Hr; destruct j; discriminate Hr)).
clear FRM HRg.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  set (rT0 := rT) in *; set (mT0 := mT) in * end.
assert (HspT : spZ rT0 = spZ regs + -48) by (unfold spZ at 1; rewrite P2, Usp; apply unsigned_lit_small; lia).
assert (P3' : getr rT0 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (P4' : getr rT0 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact Htp).
assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (P10' : getr rT0 10 = w64 wd) by (rewrite P10, (EE 12%nat 12%bv eq_refl); exact H12).
destruct (ie_word_call mT0 rT0 KEEP0 ltac:(rewrite HspT, HST, Hes; lia)) as (STRa & RDa & TLa & ROMa).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) ESTACK (fun _ => False) (SIG SS___interceptor_trampoline_strlen)
    W rT0 mT0 IE_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (-48) (Z_to_bv 64 (BASE + IE_RET)) _ HJ HspT eq_refl
    ltac:(lia) ltac:(lia) ltac:(rewrite HST, Hes; lia) P1 (fun a0 (H : False) => False_ind _ H)).
  apply (STRLEN fx ly S W rT0 mT0 _ wd (SP.zb w)).
  - exact (ecall_pre_stk_at SEGS B ESTACK IE_STK (spZ regs) [] ly S W mem md [] ly S W mT0 _ 0 rT0 (-48)
      HJ HspT eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite HST, Hes; lia) HraT P3' P4').
  - exact P10'.
  - lia.
  - exact STRa. - exact RDa. - exact TLa. - exact ROMa. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
(* back at 0x87ba8 *)
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (A52 : ew (havoc E 48 (map (getr regs2) CLOB)) 52 = getr regs2 10) by reflexivity.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ec eqn:HEc.
assert (HEI3 : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall k, (k < 48)%nat -> ew Ec k = ew E k) by (intros k Hk; rewrite HEc; apply YN3v.ew_havoc_old; exact Hk).
clear HEc.
assert (SHOK3 : sh_ok SEGS ie_Bx [] Ec (mrestrict (w_H W) mem2)) by apply Forall_nil.
assert (KEEPk : kept_out (rdW W mT0) (rdW W mem2) (spZ regs - IE_STK) (spZ regs - 48))
  by (intros x0 Hx0 Hn0; apply HK2; [exact Hx0 | rewrite Hes; lia | tauto]).
clear HK2. clear HJ. rename HJ2 into HJ.
assert (KEEPm : kept_out (rdW W mem) (rdW W mem2) (spZ regs - IE_STK) (spZ regs))
  by (apply (kept_out_trans _ _ _ _ _ _ _ KEEP0 KEEPk); lia).
assert (FR2 : ie_frame (rdW W mem2)) by exact (ie_frame_kept _ _ _ _ FR0' KEEPk ltac:(lia)).
clear KEEP0 KEEPk FR0' STRa RDa TLa ROMa.
assert (U11 : U Ec (SOff 11 0) = n).
{ apply U_atom; [rewrite OLD3, (EE 11%nat 11%bv eq_refl), H11 by lia; reflexivity | lia]. }
assert (U52 : U Ec (SOff 52 0) = Z.of_nat (length w)).
{ apply U_atom; [rewrite A52, HQ2; unfold w64, astr_len; rewrite ie_zb_length; reflexivity | lia]. }
(* 0x87ba8: bne s1,a0 *)
psrr_branch_tok RUN BR HS SHOK3 Bspan.
- (* n <> strlen(wd): 0x87c68 a0 := 0, the epilogue *)
  assert (Hne : n <> Z.of_nat (length w)).
  { rewrite branch_ne_U, U11, U52 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK3 Bspan IE_EPI.
  { awr_ok_tac. }
  ie_md.
  ie_keep_empty HFr KEEP4 (spZ regs - IE_STK) (spZ regs - IE_STK). clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (10%bv : bv 5) Q10.
  apply ie_epi.
  + split; [exact HJ|]. split; [apply (kept_out_trans _ _ _ _ _ _ _ KEEPm KEEP4); lia|].
    split; [exact (ie_frame_kept _ _ _ _ FR2 KEEP4 ltac:(lia))|].
    split; [rewrite Q2, OLD3, Usp by lia; unfold w64; f_equal; lia|].
    split; [ie_same HS ltac:(rewrite OLD3 by lia; apply EE; reflexivity)|].
    split; [ie_same HS ltac:(rewrite OLD3 by lia; apply EE; reflexivity)|].
    unfold ie_s4_11; repeat split;
      ie_same HS ltac:(rewrite OLD3 by lia; apply EE; reflexivity).
  + rewrite Q10. unfold ie_RES, SM.ieq. rewrite ie_zs_length.
    rewrite (proj2 (Nat.eqb_neq _ _)) by lia. reflexivity.
- (* n = strlen(wd): 0x87bac a0 := 1, 0x87bb0 beqz s1 *)
  assert (Heqn : n = Z.of_nat (length w)).
  { rewrite branch_ne_U, U11, U52 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK3 Bspan.
  { awr_ok_tac. }
  ie_md.
  ie_keep_empty HFr KEEP4 (spZ regs - IE_STK) (spZ regs - IE_STK). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK3 Bspan.
  + (* n = 0: 0x87c6c with a0 = 1 *)
    assert (Hz : n = 0).
    { rewrite branch_eq_U, U11, U_SLit in Hc. apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan IE_EPI.
    { awr_ok_tac. }
    ie_md.
    ie_keep_empty HFr KEEP5 (spZ regs - IE_STK) (spZ regs - IE_STK). clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (10%bv : bv 5) Q10.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
      assert (KEEPF : kept_out (rdW W mem2) (rdW W mF) (spZ regs - IE_STK) (spZ regs - IE_STK))
        by (apply (kept_out_trans _ _ _ _ _ _ _ KEEP4 KEEP5); lia) end.
    apply ie_epi.
    * split; [exact HJ|]. split; [apply (kept_out_trans _ _ _ _ _ _ _ KEEPm KEEPF); lia|].
      split; [exact (ie_frame_kept _ _ _ _ FR2 KEEPF ltac:(lia))|].
      split; [rewrite Q2, OLD3, Usp by lia; unfold w64; f_equal; lia|].
      split; [ie_same HS ltac:(rewrite OLD3 by lia; apply EE; reflexivity)|].
      split; [ie_same HS ltac:(rewrite OLD3 by lia; apply EE; reflexivity)|].
      unfold ie_s4_11; repeat split;
        ie_same HS ltac:(rewrite OLD3 by lia; apply EE; reflexivity).
    * rewrite Q10. unfold ie_RES.
      assert (Hl0 : l = []) by (apply length_zero_iff_nil; lia).
      assert (Hw0 : w = []) by (apply length_zero_iff_nil; lia).
      rewrite Hl0, Hw0. reflexivity.
  + (* n <> 0: 0x87bb4 .. 0x87bc8, a3 := snez s = 1, a4 := snez wd = 1 (folded by the entry facts ie_NZF), the
       cursors, then the loop at byte 0 *)
    assert (Hnz : 0 < n).
    { rewrite branch_eq_U, U11, U_SLit in Hc. apply Z.eqb_neq in Hc. change (zcanon 0) with 0 in Hc. lia. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan IE_LOOP.
    { awr_ok_tac. }
    ie_md.
    ie_keep_empty HFr KEEP5 (spZ regs - IE_STK) (spZ regs - IE_STK). clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
    prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
    prreg HS (15%bv : bv 5) Q15. prreg HS (16%bv : bv 5) Q16. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
      assert (KEEPF : kept_out (rdW W mem2) (rdW W mF) (spZ regs - IE_STK) (spZ regs - IE_STK))
        by (apply (kept_out_trans _ _ _ _ _ _ _ KEEP4 KEEP5); lia) end.
    apply LOOP.
    split.
    { split; [exact HJ|]. split; [apply (kept_out_trans _ _ _ _ _ _ _ KEEPm KEEPF); lia|].
      split; [exact (ie_frame_kept _ _ _ _ FR2 KEEPF ltac:(lia))|].
      split; [rewrite Q2, OLD3, Usp by lia; unfold w64; f_equal; lia|].
      split; [ie_same HS ltac:(rewrite OLD3 by lia; apply EE; reflexivity)|].
      split; [ie_same HS ltac:(rewrite OLD3 by lia; apply EE; reflexivity)|].
      unfold ie_s4_11; repeat split;
        ie_same HS ltac:(rewrite OLD3 by lia; apply EE; reflexivity). }
    split; [cbn; lia|]. split; [lia|].
    split; [rewrite Q8, OLD3, (EE 12%nat 12%bv eq_refl), H12 by lia; reflexivity|].
    split; [rewrite Q9, OLD3, (EE 11%nat 11%bv eq_refl), H11 by lia; unfold w64; f_equal; lia|].
    split; [rewrite Q10; reflexivity|].
    split; [rewrite Q11, OLD3, (EE 10%nat 10%bv eq_refl), H10 by lia; unfold w64; f_equal; lia|].
    split; [rewrite Q12, OLD3, (EE 12%nat 12%bv eq_refl), H12 by lia; unfold w64; f_equal; lia|].
    split; [rewrite Q13; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q15, OLD3, (EE 10%nat 10%bv eq_refl), H10 by lia; unfold w64; f_equal; lia|].
    split; [rewrite Q16, OLD3, (EE 12%nat 12%bv eq_refl), H12 by lia; unfold w64; f_equal; lia|].
    split; [rewrite Q18, OLD3, (EE 10%nat 10%bv eq_refl), H10 by lia; reflexivity|].
    split; [rewrite Q19, OLD3, E32 by lia; reflexivity|].
    cbn [skipn]. unfold SM.ieq. rewrite ie_zs_length.
    rewrite (proj2 (Nat.eqb_eq _ _)) by lia. reflexivity.
Qed.
Lemma ie_entry : SRr SEGS W (cfg_at SEGS (BASE + AF_ieq) regs mem md) ie_Q.
Proof.
apply ie_entry_gen. intros r m d HLP.
apply (ie_loop_all (Z.to_nat n) 0); [lia | exact HLP].
Qed.

End w.

(* ---------- the contract ---------- *)
Theorem ieq_walkB : ieq_contract SEGS B (BASE + AF_ieq) SegInstB.STK_ieq SegInstB.RLO_A SegInstB.RHI_A.
Proof.
unfold ieq_contract.
intros ly S W regs mem md ch s n wd l w HPRE HROD H10 Hs64 H11 Hn64 H12 Hw64 HIP HEV.
destruct HIP as (Hs0 & HSB & HLN & HSA & HSL & HW0 & HWS & HWA & HWL & HW32).
eapply (ie_entry ly S W regs mem md ch s n wd l w SegInstB.RLO_A SegInstB.RHI_A); eassumption.
Qed.
End e.
End d.
End b.

About ieq_walkB.
Print Assumptions ieq_walkB.
