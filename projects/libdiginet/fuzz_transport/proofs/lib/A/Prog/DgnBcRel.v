(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 274 of its 316 lines of code are new or changed and 1882 lines of the source are left out. *)
(* DgnBcRel: Lemma bc_rel : bc_rel_stmt (lib/A/Prog/DgnBcCut.v), the release piece of diginet_body_check,
   offsets +0x298 .. +0x400 of the listing lib/A/Prog/DgnDecodeList.v (fuzz_decode.asan 0x82974 .. 0x82adc).

   What the code does. +0x298 `ld a2, 24(s1)`: the frame F from the slot at sp1 + 24 (s1 = sp1); +0x29c `li a1, -8`
   and nine `sb a1, i(s7)` (i = 12 .. 16, 4 .. 7): shadow bytes of the frame (s7 = SHADOW_OFF + F / 8) := 0xf8;
   +0x2c4 `lui`/`addiw` a1 = 0x45e0360e and +0x2cc `sd a1, 0(s8)`: the frame's first word (s8 = F); +0x2d0
   `beqz a2`: a2 = F >= 4096, so the arm at +0x364 is never entered (the engine decides the branch from the atom
   fact of s8, whose value the slot holds); +0x2d4 `li a1, -11` and 32 `sb a1, i(s7)`: the frame's 32 shadow bytes
   := 0xf5; +0x358 `ld a1, 248(a2)`: the flag pointer FL from the frame's last word; +0x35c `sb zero, 0(a1)`: the
   flag byte, which releases the frame (lib/A/Prog/CanKit.v can_flag_store_pi); +0x360 `j +0x3c4`; +0x3c4
   `addi sp, s0, -160`; the 13 reloads +0x3c8 .. +0x3f8 of ra, s0, s1, s2 .. s11 from the words the prologue saved
   below the entry sp; +0x3fc `addi sp, sp, 160`; +0x400 `ret`. a0 (body_check bb at the cut) is not written.

   One run of the plain position-abstract engine (lib/A/Prog/PaSym.v sym_run_pi: no shadow token, so the writable
   shadow region is allowed) covers +0x298 .. +0x400 and stops at the `ret`, which lib/A/Prog/DgnDecodePaLib.v
   paj_ret_at takes.
   The symbolic state: the registers at +0x298 as atoms 0 .. 31, atom 32 the flag pointer FL, atoms 33 .. 45 the
   entry values of ra, s0, s1, s2 .. s11 (DgnBcCut.v BC_SAVED, in its order); regions: the slot (s1, offset 24, read:
   F = atom 24), the frame's first word (s8, written), its last word (s8, offset 248, read: FL), its 32 shadow bytes
   (s7, written), the flag byte (atom 32, written) and the 13 saved words below s0 = the entry sp (read).

   The post: the walk's own journal after the flag store has own = [] and the frame released (stack_free_state),
   and goes back into the caller's journal (ajournal_sub); what the call kept is that journal's
   (acall_kept_of_journal); the callee-saved registers are the 13 reloads, sp = s0 = the entry sp, gp and tp
   untouched; the state changed in st_fs only, so the meter bound is the cut's (mo_le_set_fs_r). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib DgnTransportCJ.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import CanKit DgnBcCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x298 and the run to the ret              *)
(* ------------------------------------------------------------------ *)

(* The `ret` of diginet_body_check. *)
Definition BC_RET : Z := AF_diginet_body_check + 0x400.

Definition rel_rg_slot : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 24 0))].
Definition rel_rg_hd : YP09.region := YP09.mkRegion (Some 24%nat) 0 8 0 8 [].
Definition rel_rg_fp : YP09.region :=
  YP09.mkRegion (Some 24%nat) 248 256 0 0 [YP09.mkChunk 248 (CVal 8 (SOff 32 0))].
Definition rel_rg_sh : YP09.region := YP09.mkRegion (Some 23%nat) 0 32 0 32 [].
Definition rel_rg_fl : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition rel_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
(* s8 = F is at least 4096 (decides the `beqz a2` at +0x2d0, a2 = the slot's F) and 32-aligned. *)
Definition rel_facts : facts := mkFacts [(24%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition ss_rel : sstate :=
  mkSS BC_REL sr_atoms [rel_rg_slot; rel_rg_hd; rel_rg_fp; rel_rg_sh; rel_rg_fl; rel_rg_sv] None rel_facts.
Definition REL_FUEL : N := 96.
Definition rel_ss_end : sstate := Eval vm_compute in fst (sym_runN_pi transport_tpi REL_FUEL ss_rel).
Definition rel_st_end : prun_status tsym := Eval vm_compute in snd (sym_runN_pi transport_tpi REL_FUEL ss_rel).
Lemma rel_run : sym_runN_pi transport_tpi REL_FUEL ss_rel = (rel_ss_end, rel_st_end).
Proof. vm_compute. reflexivity. Qed.
Lemma rel_stop : can_plain_stop rel_st_end.
Proof. exact I. Qed.
Lemma rel_end_pc : ss_pc rel_ss_end = BC_RET.
Proof. reflexivity. Qed.

(* The environment: the registers at +0x298, then FL, then the entry values of the saved registers. *)
Definition rel_extra (regs : bvmap 5 word) (FL : Z) : list word :=
  w64 FL :: map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) BC_SAVED.

(* The value of register r in the machine state of HS: its symbolic value, computed. *)
Ltac rel_regv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

Section rel. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition rel_E (regs2 regs : bvmap 5 word) (FL : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs2 (rel_extra regs FL)).

Lemma rel_ew_reg : forall regs2 regs FL n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (rel_E regs2 regs FL) n = YK11.getr regs2 r.
Proof. intros regs2 regs FL n r Hn. unfold rel_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma rel_ew_x : forall regs2 regs FL j, (j < 14)%nat ->
  ew (rel_E regs2 regs FL) (32 + j) = nth j (rel_extra regs FL) (Z_to_bv 64 0).
Proof. intros regs2 regs FL j Hj. unfold rel_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* The symbolic state at +0x298 holds of the machine state there. *)
Lemma rel_entry : forall (W : world segs) (regs2 regs : bvmap 5 word) mem (F FL SP S1 : Z),
  YK11.getr regs2 8 = w64 SP -> YK11.getr regs2 9 = w64 S1 ->
  YK11.getr regs2 23 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs2 24 = w64 F ->
  4096 <= F -> F mod 32 = 0 -> F + 256 <= alloc_ceiling -> in_app F 256 ->
  4096 <= FL < alloc_ceiling -> (FL < F \/ F + 256 <= FL) ->
  (FL < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 32 <= FL) ->
  alloc_ceiling <= S1 -> S1 + 32 <= SP - 104 -> SP <= 2 ^ 47 ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem a) ->
  (forall i, 0 <= i < 32 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  apresent (w_H W) mem FL ->
  rdword (aview segs (w_H W) mem) (S1 + 24) = Some F ->
  rdword (aview segs (w_H W) mem) (F + 248) = Some FL ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (SP - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) BC_SAVED ->
  st_ok_pi segs VAL (rel_E regs2 regs FL) ss_rel
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + BC_REL)) mem (YK11.seg_rom segs))).
Proof.
intros W regs2 regs mem F FL SP S1 R8 R9 R23 R24 HF0 HF32 HFc HFapp HFL HFLF HFLS HS1 HS1SP HSP
  Hpf Hpsh HpFL HS1w HFLw Hsaved.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF8 : F mod 8 = 0)
  by (pose proof (Z.div_mod F 32 ltac:(lia)) as D32; replace F with (F / 32 * 4 * 8) by lia; apply Z_mod_mult).
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. rewrite HF8, Z.add_0_r in D8.
set (E := rel_E regs2 regs FL).
assert (U8 : bv_unsigned (ew E 8) = SP)
  by (unfold E; rewrite (rel_ew_reg regs2 regs FL 8 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = S1)
  by (unfold E; rewrite (rel_ew_reg regs2 regs FL 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF + F / 8)
  by (unfold E; rewrite (rel_ew_reg regs2 regs FL 23 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (E24 : ew E 24 = w64 F) by (unfold E; rewrite (rel_ew_reg regs2 regs FL 24 24%bv eq_refl); exact R24).
assert (U24 : bv_unsigned (ew E 24) = F) by (rewrite E24; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (rel_ew_x regs2 regs FL 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
unfold BC_SAVED in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss_rel.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks rel_rg_slot rel_rg_hd rel_rg_fp
      rel_rg_sh rel_rg_fl rel_rg_sv base_val];
    rewrite ?U8, ?U9, ?U23, ?U24, ?U32.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ S1 24 8 (SOff 24 0) F);
      [cbn [sv_denot]; rewrite E24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ HS1w).
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ F 248 8 (SOff 32 0) FL);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ HFLw).
  + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). replace (FL + o) with FL by lia. exact HpFL.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    all: lazymatch goal with |- YP09.chunk_ok _ _ _ ?b (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      match goal with Sv : rdword _ (?b0 - ?o) = Some (bv_unsigned ?x) |- _ =>
        apply (chunk_ok_val segs E _ b off 8 (SOff n 0) (bv_unsigned x));
        [ cbn [sv_denot]; rewrite Z.add_0_r; reflexivity
        | let Hrr := fresh "Hrr" in pose proof (bv_unsigned_in_range 64 x) as Hrr;
          change (bv_modulus 64) with (2 ^ 64) in Hrr; exact Hrr
        | zside
        | replace (b + off) with (b0 - o) by lia; exact (val_mem_of_rdword segs _ _ _ _ Sv) ]
      end end.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, rel_rg_slot, rel_rg_hd, rel_rg_fp, rel_rg_sh, rel_rg_fl, rel_rg_sv.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U8, U9, U23, U24, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat split; first [exact I | lia].
- unfold rel_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U24.
  change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma bc_rel : @bc_rel_stmt fx rc B MT.
Proof.
unfold bc_rel_stmt.
intros LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F W2 regs2 mem2 md2 ly2 S2
  HFIX HCUR HREGS Ha0.
destruct LAWS0 as (HCELLS & LAWS & MTL & MTF & ASF & FFL & HREC).
destruct HFIX as (HJ0 & Hret & Hra & Hgp & Htp & Hsp16 & Hstk & Hsp0 & Hbody & Hblk & Hcnt & Hnev & Esp1 & EF &
  HF0 & HF32 & HFc & HFapp).
destruct HCUR as (HJ1 & Hperm & Hmo & Hsaved & Hlen & Hslot & HFLw & Hbb & Hsrc2).
destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R23 & R24).
unfold BC_FBYTES in HFc, HFapp, HFLw.
replace (F + 256 - 8) with (F + 248) in HFLw by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ0 as (HARc & _).
pose proof HJ1 as (HAR2 & Hly2 & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk1 & _).
pose proof Hstk1 as (_ & _ & Hceil1 & Hslo1 & Hshi1 & H47 & _).
assert (HBS : 4272 <= TRANS_BC_STK) by (unfold TRANS_BC_STK, TRANS_BC_FRAME, TRANS_BC_ALIGN, ESTACK; lia).
assert (Hsp1 : spZ regs - 192 < sp1 <= spZ regs - 160).
{ rewrite Esp1. unfold TRANS_BC_FRAME.
  pose proof (Z.div_mod (spZ regs - 160) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)) as M.
  set (q := (spZ regs - 160) / 32) in *. set (r := (spZ regs - 160) mod 32) in *. lia. }
assert (Hin : In (TRANS_BC_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose proof Hly2 as (_ & _ & _ & _ & _ & ELF & _).
assert (EFA : frame_addr ly2 TRANS_BC_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
assert (EFL : flag_addr ly2 TRANS_BC_CID pos = flag_addr lyc TRANS_BC_CID pos)
  by (unfold flag_addr; rewrite ELF; reflexivity).
rewrite <- EFL in HFLw.
destruct (al_frames _ _ LAWS _ _ _ _ _ TRANS_BC_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
destruct (FFL ly2 S2 W2 mem2 md2 TRANS_BC_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
set (FL := flag_addr ly2 TRANS_BC_CID pos) in *.
change (fs_frame_bytes TRANS_BC_CID / 8) with 32 in HFsh.
change (fs_frame_bytes TRANS_BC_CID) with 256 in HFb.
rewrite EFA in HFb, HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
assert (HFLF : FL < F \/ F + 256 <= FL).
{ destruct (Z_lt_le_dec FL F) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec FL (F + 256)) as [h2|h2]; [|right; exact h2].
  exfalso. exact (proj2 (HFb _ (conj h h2)) HFLo). }
assert (HFLS : FL < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 32 <= FL).
{ destruct (Z_lt_le_dec FL (SHADOW_OFF + F / 8)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec FL (SHADOW_OFF + F / 8 + 32)) as [h2|h2]; [|right; exact h2].
  exfalso. pose proof (proj2 (HFsh (FL - (SHADOW_OFF + F / 8)) ltac:(lia))) as Hno.
  replace (SHADOW_OFF + F / 8 + (FL - (SHADOW_OFF + F / 8))) with FL in Hno by lia.
  exact (Hno HFLo). }
pose proof (rel_entry W2 regs2 regs mem2 F FL (spZ regs) sp1 R8 R9 R23 R24 HF0 HF32 HFc HFapp
  ltac:(lia) HFLF HFLS ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i Hi)))
  HFLp Hslot HFLw Hsaved) as HS.
set (E := rel_E regs2 regs FL) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, rel_E; apply Eimg_env).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF + F / 8).
{ pose proof (Z.div_lt_upper_bound F 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  unfold E; rewrite (rel_ew_reg regs2 regs _ 23 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small;
  unfold SHADOW_OFF; lia. }
assert (U24 : bv_unsigned (ew E 24) = F)
  by (unfold E; rewrite (rel_ew_reg regs2 regs _ 24 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (rel_ew_x regs2 regs _ 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
(* +0x298 .. +0x400 in one run, the flag store at +0x35c releasing the frame. *)
refine (can_flag_store_pi (SK := tfib_sink_head) B LAWS ASF FFL W2 REL_FUEL E ss_rel rel_ss_end rel_st_end
  (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + BC_REL)) mem2 (YK11.seg_rom segs))
  TRANS_BC_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 md2 0 TRANS_BC_CID pos _ HEI HS rel_run rel_stop HJ1
  _ _ _ _).
- unfold TRANS_BC_CID. lia.
- (* the run writes the frame's first word, its shadow and the flag byte *)
  intros a (rg & Hinr & Ha). unfold ss_rel in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi rel_rg_slot rel_rg_hd rel_rg_fp rel_rg_sh rel_rg_fl
      rel_rg_sv] in Ha;
    rewrite ?U23, ?U24, ?U32 in Ha.
  + lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists TRANS_BC_CID, pos.
    split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes TRANS_BC_CID) with 256. lia.
  + lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists TRANS_BC_CID, pos.
    split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes TRANS_BC_CID / 8) with 32.
    rewrite ESH. lia.
  + right. change (flag_addr ly2 TRANS_BC_CID pos) with FL. lia.
  + lia.
- (* the flag byte is 0 after the run *)
  intros msr HSr.
  lazymatch goal with |- _ = Some _ =>
    let rr := eval vm_compute in (nth_error (ss_mem rel_ss_end) 4) in
    lazymatch rr with Some ?r4 =>
      pose proof (can_region_nth (segs := segs) _ _ msr 4 r4 HSr eq_refl) as HR4 end end.
  pose proof (can_field_of_region (segs := segs) E (ms_mem msr) 32 FL _ 0 1 0 1 0 1%N
    (SLit 0) 0 HR4 U32 ltac:(cbn [In]; auto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(cbn; lia)).
  lazymatch type of V with _ = Some (Z_to_bv 8 ?x) => replace x with 0 in V by (vm_compute; reflexivity) end.
  replace (FL + 0 + Z.of_nat 0) with FL in V by lia.
  exact V.
- (* the return *)
  intros ms2 mat2 HS2 HJ2 _ _ _.
  set (md3 := with_vm_backing (m_vm_lazy md2) mat2 md2) in *. clearbody md3.
  eapply (paj_ret_at (L := transport_listing) (PL := PL_transport) (PI := PI_transport) W2 E rel_ss_end ms2 md3 _
    HS2 eq_refl ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat3 md3).
  pose proof (ajournal_materialize segs B LAWS transport_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ2) as HJ3.
  fold md4 in HJ3. clearbody md4.
  (* the registers at the ret *)
  assert (R1e : YK11.getr (ms_regs ms2) 1 = YK11.getr regs 1).
  { rel_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10e : YK11.getr (ms_regs ms2) 10 = w64 (body_check bb)).
  { rel_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    transitivity (YK11.getr regs2 10); [apply rel_ew_reg; reflexivity | exact Ha0]. }
  assert (HP : aregs_preserved regs (ms_regs ms2)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      rel_regv HS2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    all: first
      [ reflexivity
      | transitivity (YK11.getr regs2 3); [apply rel_ew_reg; reflexivity | exact R3]
      | transitivity (YK11.getr regs2 4); [apply rel_ew_reg; reflexivity | exact R4]
      | transitivity (YK11.getr regs2 8); [apply rel_ew_reg; reflexivity|];
        rewrite R8; unfold w64, spZ; apply Z_to_bv_bv_unsigned ]. }
  assert (Hpc : v_jalr (YK11.getr (ms_regs ms2) 1) 0 = YK11.getr regs 1) by (rewrite R1e; exact Hret).
  assert (Eab' : ablocks B ly2 (stack_free_state TRANS_BC_CID pos S2) = ablocks B ly2 S2)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  unfold trans_bc_post, decode_cg_post.
  exists ly2, (stack_free_state TRANS_BC_CID pos S2), (ms_regs ms2), (ms_mem ms2), md4, 0.
  split; [rewrite Hpc; reflexivity|].
  split; [unfold TRANS_BC_EV; lia|].
  split.
  { change own with ([] ++ own).
    eapply (ajournal_sub segs B LAWS transport_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
      TRANS_BC_STK (spZ regs) [] [] ly2 (stack_free_state TRANS_BC_CID pos S2) W2 (ms_mem ms2) md4 0 HJ0 HJ3);
    [lia | lia | intros a (rg & Hrg & _); destruct Hrg]. }
  split; [exact HP|].
  split; [exact (can_sf_frames TRANS_BC_CID pos S2 (frames Sc) Hfrs)|].
  split; [rewrite Eab'; exact Hperm|].
  split.
  { eapply (acall_kept_of_journal segs B transport_segs_low TRANS_BC_STK (spZ regs) [] [] lyc Sc W memc mdc ly2
      (stack_free_state TRANS_BC_CID pos S2) W2 (ms_mem ms2) md4 0 (fun _ => False) HJ3 HARc).
    - intros a (rg & Hrg & _); destruct Hrg.
    - intros b m i Hb _ _. rewrite Eab'. eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb].
    - exact sink_closed_nil. }
  split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact Hmo|].
  exact R10e.
Qed.

End rel.
