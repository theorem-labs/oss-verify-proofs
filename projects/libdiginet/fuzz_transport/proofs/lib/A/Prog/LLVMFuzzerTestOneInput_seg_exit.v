(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 336 of its 378 lines of code are new or changed and 1882 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_exit: Lemma lc_exit_ok : lc_exit_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment EXIT of the image-A walk of fuzz_transport.asan's LLVMFuzzerTestOneInput, from the cut EXIT (lc_st_exit,
   +0x150c) to the slot post (lc_post): offsets +0x150c .. +0x1688 of the listing lib/A/Prog/DgnTransportList.v
   (0x82770 .. 0x828ec, slots 1347 .. 1442).

   What the code does. +0x150c `li a0, -8` and +0x1510 .. +0x151c `sb a0, 22(s2)` .. `sb a0, 25(s2)`: io's four
   shadow bytes become 0xf8 (s2 = SHADOW_OFF + F / 8, lc_fr); +0x1520 `lui` / +0x1524 `addiw` a0 = 0x45e0360e,
   +0x1528 `ld a1, 152(s1)` (the spill slot of F, lf_spill_sm) and +0x152c `sd a0, 0(a1)`: that value into F's first
   word; +0x1530 `ld a1, 128(s1)` (the other spill slot of F) and +0x1534 `beqz a1`: a1 = F >= 4096, so the real-stack
   arm at +0x15c8 is never entered (the engine decides the branch from the atom fact of F); +0x1538 `li a0, -11` and
   the 32 `sb a0, i(s2)`: every shadow byte of the frame becomes 0xf5; +0x15bc `ld a0, 248(a1)`: the flag pointer FL
   from F's last word; +0x15c0 `sb zero, 0(a0)`: the flag byte, which releases the frame (lib/A/Prog/TransportGFrame.v
   gx_flag_store_pi over astack_free_law); +0x15c4 `j +0x1648`; +0x1648 `li a0, 0`; +0x164c `addi sp, s0, -320`; the
   13 reloads +0x1650 .. +0x1680 of ra, s0, s1, s2 .. s11 from the words the prologue saved below the entry sp
   (segs.v LF_SAVED, lc_saved); +0x1684 `addi sp, sp, 320`; +0x1688 `ret`. No call, no instrumented check.

   One run of the plain position-abstract engine (lib/A/Prog/PaSym.v sym_run_pi: no shadow token, so the writable
   shadow region is allowed) covers +0x150c .. +0x1688 and stops at the `ret`, which lib/A/Prog/DgnTransportPaLib.v
   paj_ret_at takes. The symbolic state: the registers at +0x150c as atoms 0 .. 31, atom 32 the frame F, atom 33 the
   flag pointer FL, atoms 34 .. 46 the entry values of ra, s0, s1, s2 .. s11 (LF_SAVED, in its order); regions: the two
   spill slots of F at s1 + 128 and s1 + 152 (read), F's first word (written), F's last word (read: FL), the 32 shadow
   bytes at s2 (written), the flag byte (written) and the 13 saved words below s0 = the entry sp (read).

   The post (segs.v lc_post, lib/A/ACfn.v tfib_lib_post_x). The journal: the cut's G journal at FP = [] after the flag
   store, with own = [] and the frame released (stack_free_state), widened to the post's FP = [sink_token] by
   LLVMFuzzerTestOneInput_st.v lc_fp_token. The events: e <= RECV_EV * k <= 2 * OPS_MAX = EV_LIB. The callee-saved
   registers are the 13 reloads, sp = s0 = the entry sp, gp / tp the cut's (the entry's); a0 = 0; the return to the
   caller's ra (ret_ok, raZ = RA_LLVMF). The blocks: the cut's (stack_free_state keeps them). The file descriptors and
   m_fs: the entry's, by lc_journal_io at FP = []. asink_none by lp_sink_kept at FP = [] (YCbq.v sink_closed_nil);
   ameta_inv by lp_meta_kept. The meter: the cut's mo_le at k * lf_rcost (the run changes st_fs only:
   mo_le_set_fs_r), with k <= OPS_MAX, lf_cost_eq and lp_cost: k * rcost <= OPS_MAX * rcost = cost <= XL n. The input
   bytes: the cut's lc_input, kept by the run, whose written bytes (the frame, its shadow, its flag byte:
   TransportGCg.v dkg_nf) are apart from every block (TransportGFrame.v dkg_nf_sep_gw). No kit statement K1 .. K7 is
   used. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TCb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x150c and the run to the ret             *)
(* ------------------------------------------------------------------ *)

(* The two spill slots of F at s1 (atom 9), each holding F (atom 32); F's first word (atom 32), written; F's last word
   (atom 32, offset 248), holding FL (atom 33); the 32 shadow bytes at s2 (atom 18), written; the flag byte (atom 33),
   written; the 13 saved words below s0 (atom 8): the word at s0 - o holds atom 34 + i for the i-th entry (o, r) of
   LF_SAVED. *)
Definition ex_rg_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 128 160 0 0
    [YP09.mkChunk 128 (CVal 8 (SOff 32 0)); YP09.mkChunk 152 (CVal 8 (SOff 32 0))].
Definition ex_rg_hd : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 8 [].
Definition ex_rg_fp : YP09.region :=
  YP09.mkRegion (Some 32%nat) 248 256 0 0 [YP09.mkChunk 248 (CVal 8 (SOff 33 0))].
Definition ex_rg_sh : YP09.region := YP09.mkRegion (Some 18%nat) 0 32 0 32 [].
Definition ex_rg_fl : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [].
Definition ex_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 34 0)); YP09.mkChunk (-16) (CVal 8 (SOff 35 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 36 0)); YP09.mkChunk (-32) (CVal 8 (SOff 37 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 38 0)); YP09.mkChunk (-48) (CVal 8 (SOff 39 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 40 0)); YP09.mkChunk (-64) (CVal 8 (SOff 41 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 42 0)); YP09.mkChunk (-80) (CVal 8 (SOff 43 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 44 0)); YP09.mkChunk (-96) (CVal 8 (SOff 45 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 46 0))].
(* F is at least 4096 (decides the `beqz a1` at +0x1534) and 32-aligned. *)
Definition ex_facts : facts := mkFacts [(32%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition ss_ex : sstate :=
  mkSS LO_EXIT sr_atoms [ex_rg_sp; ex_rg_hd; ex_rg_fp; ex_rg_sh; ex_rg_fl; ex_rg_sv] None ex_facts.
Definition EX_FUEL : N := 96.
Definition ex_ss_end : sstate := Eval vm_compute in fst (sym_runN_pi transport_tpi EX_FUEL ss_ex).
Definition ex_st_end : prun_status tsym := Eval vm_compute in snd (sym_runN_pi transport_tpi EX_FUEL ss_ex).
Lemma ex_run : sym_runN_pi transport_tpi EX_FUEL ss_ex = (ex_ss_end, ex_st_end).
Proof. vm_compute. reflexivity. Qed.
Lemma ex_stop : can_plain_stop ex_st_end.
Proof. exact I. Qed.
(* The run stops at the `ret`, +0x1688. *)
Lemma ex_end_pc : ss_pc ex_ss_end = 0x1688.
Proof. reflexivity. Qed.

(* The environment: the registers at +0x150c, then F, FL and the entry values of the saved registers. *)
Definition ex_extra (regs : bvmap 5 word) (F FL : Z) : list word :=
  w64 F :: w64 FL :: map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) LF_SAVED.

(* The value of register r in the machine state of HS: its symbolic value, computed. *)
Ltac ex_regv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

Section en. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition ex_E (regs2 regs : bvmap 5 word) (F FL : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs2 (ex_extra regs F FL)).

Lemma ex_ew_reg : forall regs2 regs F FL n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (ex_E regs2 regs F FL) n = YK11.getr regs2 r.
Proof. intros regs2 regs F FL n r Hn. unfold ex_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma ex_ew_x : forall regs2 regs F FL j, (j < 15)%nat ->
  ew (ex_E regs2 regs F FL) (32 + j) = nth j (ex_extra regs F FL) (Z_to_bv 64 0).
Proof. intros regs2 regs F FL j Hj. unfold ex_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* The symbolic state at +0x150c holds of the machine state there. *)
Lemma ex_entry : forall (W : world segs) (regs2 regs : bvmap 5 word) mem (F FL SP SP1 : Z),
  YK11.getr regs2 8 = w64 SP -> YK11.getr regs2 9 = w64 SP1 ->
  YK11.getr regs2 18 = w64 (SHADOW_OFF + F / 8) ->
  4096 <= F -> F mod 32 = 0 -> F + 256 <= alloc_ceiling -> in_app F 256 ->
  4096 <= FL < alloc_ceiling -> (FL < F \/ F + 256 <= FL) ->
  (FL < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 32 <= FL) ->
  alloc_ceiling <= SP1 -> SP1 + 320 <= SP -> SP <= 2 ^ 47 ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem a) ->
  (forall i, 0 <= i < 32 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  apresent (w_H W) mem FL ->
  rdword (aview segs (w_H W) mem) (F + 248) = Some FL ->
  rdword (aview segs (w_H W) mem) (SP1 + 128) = Some F ->
  rdword (aview segs (w_H W) mem) (SP1 + 152) = Some F ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (SP - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) LF_SAVED ->
  st_ok_pi segs VAL (ex_E regs2 regs F FL) ss_ex
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + LO_EXIT)) mem (YK11.seg_rom segs))).
Proof.
intros W regs2 regs mem F FL SP SP1 R8 R9 R18 HF0 HF32 HFc HFapp HFL HFLF HFLS HSP1c HSP1 HSP47
  Hpf Hpsh HpFL HFLw Hs128 Hs152 Hsaved.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF8 : F mod 8 = 0)
  by (pose proof (Z.div_mod F 32 ltac:(lia)) as D32; replace F with (F / 32 * 4 * 8) by lia; apply Z_mod_mult).
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. rewrite HF8, Z.add_0_r in D8.
set (E := ex_E regs2 regs F FL).
assert (U8 : bv_unsigned (ew E 8) = SP)
  by (unfold E; rewrite (ex_ew_reg regs2 regs F FL 8 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = SP1)
  by (unfold E; rewrite (ex_ew_reg regs2 regs F FL 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF + F / 8)
  by (unfold E; rewrite (ex_ew_reg regs2 regs F FL 18 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = w64 F) by exact (ex_ew_x regs2 regs F FL 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (E33 : ew E 33 = w64 FL) by exact (ex_ew_x regs2 regs F FL 1 ltac:(lia)).
assert (U33 : bv_unsigned (ew E 33) = FL) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
unfold LF_SAVED in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss_ex.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ex_rg_sp ex_rg_hd ex_rg_fp ex_rg_sh
      ex_rg_fl ex_rg_sv base_val];
    rewrite ?U8, ?U9, ?U18, ?U32, ?U33.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val segs E _ SP1 128 8 (SOff 32 0) F);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword segs _ _ _ _ Hs128).
    * apply (chunk_ok_val segs E _ SP1 152 8 (SOff 32 0) F);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword segs _ _ _ _ Hs152).
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ F 248 8 (SOff 33 0) FL);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
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
  unfold extent_of_region, ex_rg_sp, ex_rg_hd, ex_rg_fp, ex_rg_sh, ex_rg_fl, ex_rg_sv.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U8, U9, U18, U32, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat split; first [exact I | lia].
- unfold ex_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32.
  change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
End en.

(* ------------------------------------------------------------------ *)
(* 2. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Section x. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma lc_exit_ok : lc_exit_stmt B MT XL RLO RHI.
Proof.
unfold lc_exit_stmt. intros HP cx W' c' HB HX.
destruct HX as (ly' & S' & regs' & mem' & md' & e & k & Ec & HC & HFR & HSP & _ & Hk & He & (Hmle & _)).
subst c'.
lazymatch goal with |- SRr _ _ _ ?Q => remember Q as QP eqn:EQP end.
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (lp_meter_laws B MT XL RLO RHI HP) as MTL.
pose proof (lp_meter_fs_laws B MT XL RLO RHI HP) as MTF.
pose proof (lp_asf B MT XL RLO RHI HP) as ASF.
pose proof (lp_ffl B MT XL RLO RHI HP) as FFL.
pose proof (lp_sink_kept B MT XL RLO RHI HP) as HSINK.
pose proof (lp_meta_kept B MT XL RLO RHI HP) as HMETA.
pose proof (lp_cost B MT XL RLO RHI HP) as HCOST.
clear HP.
(* the slot's pre: the return address, gp / tp, the file system, the sink and the metadata at the entry *)
pose proof HB as HB'. unfold lc_base, tfib_lib_pre_x in HB'.
destruct HB' as (HAFN & Hra & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsink0 & _ & Hfss & Hmeta0 & _).
destruct HAFN as (_ & Hret0 & _ & Hgp0 & Htp0 & _).
(* the cut's core and geometry *)
destruct (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC)
  as [HAR _ Hstk Hsp1c HFaddr HFin Hn HIN _].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & _ & R8 & R9 & R3 & R4 & Hsp1 & _ & HSAV & HF4096 & HF64 & HFceil & _ &
  HFLw & HINP).
pose proof HFR as (R18 & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold LF_FRAME in Hsp1. unfold LF_FBYTES in HFceil.
replace (lc_F cx + LF_FBYTES - 8) with (lc_F cx + 248) in HFLw by (unfold LF_FBYTES; lia).
assert (HF32 : lc_F cx mod 32 = 0).
{ pose proof (Z.div_mod (lc_F cx) 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (lc_F cx / 64)) with ((2 * (lc_F cx / 64)) * 32) by lia. apply Z_mod_mult. }
(* the frame, its shadow bytes and its flag byte at the cut *)
destruct (al_frames _ _ LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) HAR HFin) as (_ & HFapp & HFb & HFsh).
change (fs_frame_bytes LF_CID / 8) with 32 in HFsh.
change (fs_frame_bytes LF_CID) with 256 in HFapp, HFb.
rewrite HFaddr in HFapp, HFb, HFsh.
assert (ESH : shadow_addr (lc_F cx) = SHADOW_OFF + lc_F cx / 8) by reflexivity.
rewrite ESH in HFsh.
destruct (FFL ly' S' W' mem' md' LF_CID (l_fpos cx) HAR HFin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
assert (EFL : flag_addr ly' LF_CID (l_fpos cx) = lc_FL cx) by (unfold lc_FL, flag_addr; rewrite HlyF; reflexivity).
rewrite EFL in HFLp, HFLo, HFL4096, HFLc.
assert (HFLF : lc_FL cx < lc_F cx \/ lc_F cx + 256 <= lc_FL cx).
{ destruct (Z_lt_le_dec (lc_FL cx) (lc_F cx)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec (lc_FL cx) (lc_F cx + 256)) as [h2|h2]; [|right; exact h2].
  exfalso. exact (proj2 (HFb _ (conj h h2)) HFLo). }
assert (HFLS : lc_FL cx < SHADOW_OFF + lc_F cx / 8 \/ SHADOW_OFF + lc_F cx / 8 + 32 <= lc_FL cx).
{ destruct (Z_lt_le_dec (lc_FL cx) (SHADOW_OFF + lc_F cx / 8)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec (lc_FL cx) (SHADOW_OFF + lc_F cx / 8 + 32)) as [h2|h2]; [|right; exact h2].
  exfalso. pose proof (proj2 (HFsh (lc_FL cx - (SHADOW_OFF + lc_F cx / 8)) ltac:(lia))) as Hno.
  replace (SHADOW_OFF + lc_F cx / 8 + (lc_FL cx - (SHADOW_OFF + lc_F cx / 8))) with (lc_FL cx) in Hno by lia.
  exact (Hno HFLo). }
(* the two spill slots of F and the saved words *)
unfold lc_spills, lf_spill_sm in HSP.
apply Forall_cons_iff in HSP as [Hs128 HSP]. apply Forall_cons_iff in HSP as [Hs152 _].
cbn [fst snd] in Hs128, Hs152.
unfold lc_saved in HSAV.
(* the own frame, its shadow bytes and its flag byte are apart from every block *)
assert (HfrsSF : frames S' = (LF_CID, l_fpos cx) :: frames (stack_free_state LF_CID (l_fpos cx) S')).
{ rewrite (can_sf_frames LF_CID (l_fpos cx) S' [] Hfrs). exact Hfrs. }
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low ly' (stack_free_state LF_CID (l_fpos cx) S') ly' S' W' mem' md'
  LF_CID (l_fpos cx) (lc_F cx) (lc_FL cx) HAR HfrsSF (fun bm Hb => Hb) eq_refl (eq_sym HFaddr) (eq_sym EFL) FFL)
  as (N1 & _ & _ & _).
(* the symbolic state at +0x150c *)
pose proof (ex_entry (fx := l_fx cx) W' regs' (l_regs cx) mem' (lc_F cx) (lc_FL cx) (lc_sp0 cx) (lc_sp1 cx)
  R8 R9 R18 HF4096 HF32 HFceil HFapp (conj HFL4096 HFLc) HFLF HFLS ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i Hi)))
  HFLp HFLw Hs128 Hs152 HSAV) as HS.
set (E := ex_E regs' (l_regs cx) (lc_F cx) (lc_FL cx)) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ex_E; apply Eimg_env).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF + lc_F cx / 8).
{ pose proof (Z.div_lt_upper_bound (lc_F cx) 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)).
  unfold E; rewrite (ex_ew_reg regs' (l_regs cx) _ _ 18 18%bv eq_refl), R18; unfold w64, lc_SH;
  apply unsigned_lit_small; unfold SHADOW_OFF; lia. }
assert (E32 : ew E 32 = w64 (lc_F cx)) by exact (ex_ew_x regs' (l_regs cx) _ _ 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = lc_F cx) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (E33 : ew E 33 = w64 (lc_FL cx)) by exact (ex_ew_x regs' (l_regs cx) _ _ 1 ltac:(lia)).
assert (U33 : bv_unsigned (ew E 33) = lc_FL cx) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + LO_EXIT)) mem'
    (YK11.seg_rom segs)) md') Q) end.
(* +0x150c .. +0x1688 in one run, the flag store at +0x15c0 releasing the frame. *)
refine (gx_flag_store_pi (SK := tfib_sink_head) B LAWS ASF FFL TG.G_HARNESS W' EX_FUEL E ss_ex ex_ss_end ex_st_end
  (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + LO_EXIT)) mem' (YK11.seg_rom segs))
  LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [] ly' S' md' e LF_CID (l_fpos cx) _
  HEI HS ex_run ex_stop HJ _ _ _ _).
- unfold LF_CID. lia.
- (* the run writes F's first word, the frame's shadow and the flag byte *)
  intros a (rg & Hinr & Ha). unfold ss_ex in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi ex_rg_sp ex_rg_hd ex_rg_fp ex_rg_sh ex_rg_fl ex_rg_sv] in Ha;
    rewrite ?U18, ?U32, ?U33 in Ha.
  + lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists LF_CID, (l_fpos cx).
    split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. lia.
  + lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists LF_CID, (l_fpos cx).
    split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite HFaddr. change (fs_frame_bytes LF_CID / 8) with 32.
    rewrite ESH. lia.
  + right. rewrite EFL. lia.
  + lia.
- (* the flag byte is 0 after the run *)
  intros msr HSr.
  lazymatch goal with |- _ = Some _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ex_ss_end) 4) in
    lazymatch rr with Some ?r4 =>
      pose proof (can_region_nth (segs := segs) _ _ msr 4 r4 HSr eq_refl) as HR4 end end.
  pose proof (can_field_of_region (segs := segs) E (ms_mem msr) 33 (lc_FL cx) _ 0 1 0 1 0 1%N
    (SLit 0) 0 HR4 U33 ltac:(cbn [In]; auto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(cbn; lia)).
  lazymatch type of V with _ = Some (Z_to_bv 8 ?x) => replace x with 0 in V by (vm_compute; reflexivity) end.
  rewrite EFL. replace (lc_FL cx + 0 + Z.of_nat 0) with (lc_FL cx) in V by lia.
  exact V.
- (* the return *)
  intros ms2 mat2 HS2 HJ2 _ HF2 _.
  set (md3 := with_vm_backing (m_vm_lazy md') mat2 md') in *. clearbody md3.
  (* what the run kept: every byte outside the frame, its shadow bytes and its flag byte *)
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ dkg_nf LF_CID (lc_F cx) (lc_FL cx) a ->
    aview segs (w_H W') (ms_mem ms2) a = aview segs (w_H W') mem' a).
  { apply (kept_of_frame (segs := segs) E (ss_mem ss_ex) (w_H W') mem' (ms_mem ms2) _ HF2).
    intros b wlo whi x Hw Hx. unfold ss_ex, windows in Hw.
    cbn [ss_mem map In YP09.r_base YP09.r_wlo YP09.r_whi ex_rg_sp ex_rg_hd ex_rg_fp ex_rg_sh ex_rg_fl ex_rg_sv]
      in Hw.
    unfold dkg_nf. change (fs_frame_bytes LF_CID / 8) with 32. change (fs_frame_bytes LF_CID) with 256.
    destruct Hw as [Hw | [Hw | [Hw | [Hw | [Hw | [Hw | []]]]]]]; injection Hw as <- <- <-;
      cbn [base_val] in Hx; rewrite ?U18, ?U32, ?U33 in Hx.
    + lia.
    + left. lia.
    + lia.
    + right; left. lia.
    + right; right. lia.
    + lia. }
  eapply (paj_ret_at (fx := l_fx cx) (PL := PL_transport) (PI := PI_transport) W' E ex_ss_end ms2 md3 _
    HS2 eq_refl ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat3 md3).
  pose proof (ajournal_gx_materialize segs B LAWS transport_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ2)
    as HJ3.
  fold md4 in HJ3. clearbody md4.
  (* the registers at the ret *)
  assert (R1e : YK11.getr (ms_regs ms2) 1 = YK11.getr (l_regs cx) 1).
  { ex_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10e : YK11.getr (ms_regs ms2) 10 = w64 0).
  { ex_regv HS2. reflexivity. }
  assert (HPR : aregs_preserved (l_regs cx) (ms_regs ms2)).
  { intros rr Hr. unfold acallee_saved in Hr.
    assert (Hr' : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
      rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      ex_regv HS2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    all: first
      [ reflexivity
      | transitivity (YK11.getr regs' 3); [apply ex_ew_reg; reflexivity | exact (eq_trans R3 (eq_sym Hgp0))]
      | transitivity (YK11.getr regs' 4); [apply ex_ew_reg; reflexivity | exact (eq_trans R4 (eq_sym Htp0))]
      | transitivity (YK11.getr regs' 8); [apply ex_ew_reg; reflexivity|];
        rewrite R8; unfold w64, lc_sp0, spZ; apply Z_to_bv_bv_unsigned ]. }
  assert (Hpc : v_jalr (YK11.getr (ms_regs ms2) 1) 0 = w64 RA_LLVMF).
  { rewrite R1e. unfold YK0s.ret_ok in Hret0. rewrite Hret0. rewrite <- Hra. unfold w64, raZ.
    symmetry. apply Z_to_bv_bv_unsigned. }
  (* the file descriptors and the file system: the entry's (the journal at FP = []) *)
  destruct (lc_journal_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (Efd & Efs).
  destruct Hn as ((Hn0 & _) & _).
  subst QP. unfold lc_post.
  exists ly', (stack_free_state LF_CID (l_fpos cx) S'), (ms_regs ms2), (ms_mem ms2), md4, e.
  split; [unfold cfg_at; rewrite Hpc; reflexivity|].
  unfold tfib_lib_post_x.
  split; [exact (lc_fp_token B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)|].
  split.
  { assert (EV : receive_cg.RECV_EV = 2) by reflexivity. assert (EO : TC.OPS_MAX = 1024) by reflexivity.
    rewrite EV in He. unfold EV_LIB. lia. }
  split; [exact HPR|].
  split; [exact R10e|].
  split; [unfold ablocks; rewrite blocks_stack_free_state; exact HPERM|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hfss|].
  split; [exact (HSINK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 sink_closed_nil Hsink0)|].
  split; [exact (HMETA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 Hmeta0)|].
  split.
  { (* the meter: k receive budgets, k <= OPS_MAX, within the cost *)
    unfold stack_free_state. apply (mo_le_set_fs_r MT MTF). apply (mo_le_mono MT MTL _ _ _ _ Hmle).
    pose proof (HCOST (l_n cx) Hn0) as Hc. rewrite lf_cost_eq in Hc.
    assert (Hr : 0 <= lf_rcost MT).
    { unfold lf_rcost. pose proof (mo_malloc_nonneg MT MTL 65535 ltac:(lia)). pose proof (mo_free_nonneg MT MTL).
      lia. }
    assert (Hkr : k * lf_rcost MT <= TC.OPS_MAX * lf_rcost MT)
      by (apply Z.mul_le_mono_nonneg_r; [exact Hr | exact (proj2 Hk)]).
    exact (Z.le_trans _ _ _ Hkr Hc). }
  (* the input bytes: the cut's, kept by the run *)
  intros i Hi.
  destruct (Z_lt_le_dec 0 (l_n cx)) as [Hnp | Hnp]; [|lia].
  pose proof (HIN Hnp) as InP.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ (l_p cx) (l_n cx) HAR InP) as (_ & Hb4096 & Hbce & _).
  pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
  rewrite (KP (l_p cx + i) ltac:(lia) ltac:(intros Hd; exact (N1 (l_p cx) (l_n cx) i InP ltac:(lia) Hd))).
  exact (proj2 HINP i Hi).
Qed.

End x.
