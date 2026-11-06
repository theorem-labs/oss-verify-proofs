(* pj_write 0x83d08 (preset_file.c:654-668) on fs.asan, image A: the ASan walk of lib/A/FSH_Fn_writer.v's
   `pj_write_spec`, over the walk kit lib/A/FSW_K.v (a Theorem Labs lane) and lib/A/FSW_ret.v (a Theorem Labs lane).

   The function builds a 32-byte `struct pj_out` on its OWN REAL stack (no fake frame; FRAME_pj_write = 64, the
   object at entry sp - 56 .. sp - 24, the saved s1 / s0 / ra at sp - 24 / sp - 16 / sp - 8), zeroes it with
   __asan_memset (PC_memset 0x521bc, return PJW_MS_RET 0x83d30), calls write_value at level 0 with
   ot = sp - 16 (the first 16-aligned address above the object's end; FSH_Fn_FORM.md section 3a), then - when
   pretty - `put` of the final newline, and finally returns the buffer, or fuzz_free's it and returns NULL.
   Addresses (generation-N proof of this function over the same image, commit 211ff3e9df0
   lib/A/Prog/pj_write_blocks.v:9-18, text only, not in this tree): PJ_WRITE 0x83d08, CHECKED_MEMSET 0x521bc,
   PJW_MS_RET 0x83d30, WRITE_VALUE 0x83d84, PJW_WV_RET 0x83d44, PUT 0x8418c, PJW_PUT_RET 0x83d5c,
   FUZZ_FREE 0x82d40, PJW_FREE_RET 0x83d6c, the epilogue 0x83d70, STR_NL 0x21040.

   Callees are premises of the closing theorem pjw_pj_write_spec (end of file), never walks this file waits for:
   write_value at level 0, put, fuzz_free (lib/A/FSH_Fn_alloc.v), and fs_img_facts (the "\n" literal); the runtime
   __asan_memset is the Section hypothesis RT (FSH_Rt.v's FsRt, field fr_memset, in ARU form).

   Rule 24 (proof-index v5 built 2026-10-28T21:58:24Z, exit 0, read from a file, not a pipe; re-checked by
   a Theorem Labs lane 2026-10-28T22:32Z): pj_write has RELEASED proofs for fs's PLAIN and UBSAN builds only
   (lib/Prog, lib/U/Prog, ossv/recipes@566eb6ffa5, release/pau-projects-recipes@b6a0088adc), none for an ASan
   build. Those plain contracts / proofs are templates here, not drop-ins. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat
FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model FSW_writer_kit
FSH_Fn_reader FSW_rd FSupoisonStack.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct WriterAppFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the walk's own addresses inside pj_write (see the header for where they come from) *)
Definition PJW_MS_RET : Z := 0x83d30.
Definition PJW_WV_RET : Z := 0x83d44.
Definition PJW_PUT_RET : Z := 0x83d5c.
Definition PJW_FREE_RET : Z := 0x83d6c.
Definition PJW_STR_NL : Z := 0x21040.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the runtime interface at this build's PC_* (S0 lib/A/FSH_Rt.v): the walk uses fr_memset only *)
(* only the PC_memset interceptor's contract, FSH_Rt.v's FsRt field fr_memset: the walk projects nothing else from the
   runtime record, so it takes just this field - in particular NOT fr_snprintf (a Theorem Labs lane's A6). *)
Hypothesis RT_memset : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.


(* ---- premise discharge for the __asan_memset call. The ASan shadow of the whole stack band reads 0 (AR's
   am_zshadow at zero_shadow_ranges' head, Reusable/YG0n.v:187-190), and the raw memory reads a stack shadow cell
   as the unpoisoned one does (kit: FSupoisonStack.fsw_ARU_stack_cell_view), so the intrinsic's two shadow
   premises hold on the machine's OWN memory. Not a kit step: the data-premise side of one call, as FSW_rd.v
   does for the reader's premises. ---- *)
Lemma pjw_stack_shadow : forall (W : world tfibsegs) ly S U mem md a n,
  ARU tfibsegs B ly S U W mem md ->
  ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly -> 0 <= n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF a n /\
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) a n).
Proof.
intros W ly S U mem md a n HARU Hlo Hhi Hn.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HAR : AR tfibsegs B ly S W (unpoison U mem) md) by (destruct HARU as (H1 & _ & _); exact H1).
assert (OKU : upoison_ok B ly S U) by (destruct HARU as (_ & H2 & _); exact H2).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & Lpt & Lhi & Lplo & Lphi & Lbeg).
unfold page_aligned in Lplo, Lphi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (al_zshadow _ _ LAWS ly S W (unpoison U mem) md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz. unfold zero_shadow in Hz.
(* the band's shadow cells read the same in the raw and the unpoisoned memory (kit) *)
assert (HU : forall s, SHADOW_OFF + ly_stk_lo ly / 8 <= s < SHADOW_OFF + ly_stk_hi ly / 8 ->
  aview tfibsegs (w_H W) mem s = aview tfibsegs (w_H W) (unpoison U mem) s).
{ intros s Hs. symmetry. apply (fsw_ARU_stack_cell_view tfibsegs B LAWS ly S U W mem md (w_H W) s HARU).
  unfold shadow_addr, SHADOW_OFF, kHighMemEnd in *. lia. }
split.
- intros y Hy. exists 0. split; [|left; reflexivity].
  rewrite HU by (unfold shadow_of_addr; lia).
  replace (shadow_of_addr SHADOW_OFF y)
    with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8)) by (unfold shadow_of_addr; lia).
  apply Hz. lia.
- intros Hn0 s Hs.
  assert (Hsr : SHADOW_OFF + ly_stk_lo ly / 8 <= s < SHADOW_OFF + ly_stk_hi ly / 8).
  { unfold shadow_addr in Hs. unfold SHADOW_OFF in *. lia. }
  rewrite HU by exact Hsr.
  replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly)))
    by (unfold shadow_of_addr; lia).
  rewrite Hz; [discriminate|]. unfold shadow_of_addr, SHADOW_OFF in *. lia.
Qed.

(* a register the entry run left as its own atom (no evar reaches vm_compute: k is read off the goal) *)
Local Ltac pjw_c_atom H r0 ex ms HS :=
  match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    exact (fsw_reg_atom H r0 ex _ ms (Z_to_bv 5 k) (Z_to_bv 5 k) (Z.to_nat k) HS
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) end.

(* ================= stage 1: the entry, the frame, the pj_out address, up to the __asan_memset call =================
   0x83d08 .. 0x83d2c (10 instructions, no call, no inline shadow check): `addi sp, sp, -64`, the three saves,
   `mv s0, a1` (pretty), `mv s1, a0` (v), the memset arguments a0 = sp - 56, a1 = 0, a2 = 32, `jal __asan_memset`.
   The run stops at 0x521bc, which the writer table does not hold. *)
Lemma pjw_to_memset : forall (W : world tfibsegs) ly S U regs mem md ch (Q : world tfibsegs -> config -> Prop),
  afn_preU tfibsegs B STK_pj_write ly S U W regs mem md ch ->
  (forall regs1 mem1 md1,
     ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
       ly S W (unpoison U mem1) md1 0 ->
     ARU tfibsegs B ly S U W mem1 md1 ->
     same_below mem mem1 alloc_ceiling ->
     spZ regs1 = spZ regs - FRAME_pj_write ->
     getr regs1 1 = w64 PJW_MS_RET ->
     getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
     getr regs1 8 = getr regs 11 -> getr regs1 9 = getr regs 10 ->
     getr regs1 10 = w64 (spZ regs - 56) -> getr regs1 11 = w64 0 -> getr regs1 12 = w64 32 ->
     val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
     val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 16) 8 (s0Z regs) ->
     val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 8) 8 (raZ regs) ->
     (forall q : bv 5, 18 <= bv_unsigned q <= 27 -> getr regs1 q = getr regs q) ->
     SRr tfibsegs W (cfg_at tfibsegs PC_memset regs1 mem1 md1) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_pj_write regs mem md) Q.
Proof.
intros W ly S U regs mem md ch Q HPRE K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
pose proof HPRE as (HAP & _ & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPRE) as HARU.
assert (HFR : 0 <= FRAME_pj_write <= STK_pj_write) by (vm_compute; split; discriminate).
pose proof (fsw_entry B STK_pj_write FRAME_pj_write ly S U W regs mem md ch A_pj_write HPRE HFR
  ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_pj_write FS_PSTAT_FP ly S W regs (unpoison U mem) md ch HAP) as HJ.
set (E := Ereg regs []) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (subst E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_pj_write) with (Z_to_bv 64 A_pj_write).
fsw_aj_runU fsw_wr_tbl_ok HS HJ HARU.
{ awr_ok_tac. exact Usp. }
(* the run wrote only the frame window [sp - 64, sp) *)
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ change (frame_of E [fstk FRAME_pj_write] mem (ms_mem ms)) in HF.
  apply (same_below_frame1 E (fstk FRAME_pj_write) mem (ms_mem ms) alloc_ceiling HF); [|lia].
  cbn [fstk YP09.r_base YP09.r_wlo base_val]. rewrite Usp. unfold FRAME_pj_write in *. lia. }
pose proof (fsw_reg_lit (w_H W) E _ ms 1%bv PJW_MS_RET HS ltac:(vm_compute; reflexivity)
  ltac:(unfold PJW_MS_RET; lia)) as R1.
pose proof (fsw_reg_off (w_H W) E _ ms 2%bv 2 (- FRAME_pj_write) (spZ regs) HS
  ltac:(vm_compute; reflexivity) Usp ltac:(unfold FRAME_pj_write in *; lia)) as R2.
pose proof (fsw_reg_atom (w_H W) regs [] _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom (w_H W) regs [] _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom (w_H W) regs [] _ ms 8%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fsw_reg_atom (w_H W) regs [] _ ms 9%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R9.
pose proof (fsw_reg_off (w_H W) E _ ms 10%bv 2 (-56) (spZ regs) HS
  ltac:(vm_compute; reflexivity) Usp ltac:(unfold FRAME_pj_write in *; lia)) as R10.
pose proof (fsw_reg_lit (w_H W) E _ ms 11%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R11.
pose proof (fsw_reg_lit (w_H W) E _ ms 12%bv 32 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R12.
(* the three saved words, read off the frame region of the state at the call *)
pose proof (fsw_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (fsw_field E _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HR0 Usp ltac:(cbn; tauto)
  ltac:(rewrite fsw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 1 1%bv eq_refl); unfold raZ; symmetry;
        apply Z_to_bv_bv_unsigned)
  ltac:(unfold raZ; apply u64_range) ltac:(cbn; lia)) as Vra.
pose proof (fsw_field E _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) (s0Z regs) HR0 Usp ltac:(cbn; tauto)
  ltac:(rewrite fsw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 8 8%bv eq_refl); unfold s0Z; symmetry;
        apply Z_to_bv_bv_unsigned)
  ltac:(unfold s0Z; apply u64_range) ltac:(cbn; lia)) as Vs0.
pose proof (fsw_field E _ 2 (spZ regs) _ _ _ _ _ (-24) 8%N (SOff 9 0) (bv_unsigned (getr regs 9)) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(rewrite fsw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 9 9%bv eq_refl); symmetry;
        apply Z_to_bv_bv_unsigned)
  ltac:(apply u64_range) ltac:(cbn; lia)) as Vs1.
clear HR0.
(* s2 .. s11: the run does not touch them *)
assert (Rs : forall q : bv 5, 18 <= bv_unsigned q <= 27 -> getr (ms_regs ms) q = getr regs q).
{ intros q Hq. rewrite <- (Z_to_bv_bv_unsigned 5 q).
  assert (Hc : bv_unsigned q = 18 \/ bv_unsigned q = 19 \/ bv_unsigned q = 20 \/ bv_unsigned q = 21 \/
               bv_unsigned q = 22 \/ bv_unsigned q = 23 \/ bv_unsigned q = 24 \/ bv_unsigned q = 25 \/
               bv_unsigned q = 26 \/ bv_unsigned q = 27) by lia.
  repeat (destruct Hc as [Eq|Hc]; [rewrite Eq; pjw_c_atom (w_H W) regs (@nil word) ms HS|]).
  rewrite Hc. pjw_c_atom (w_H W) regs (@nil word) ms HS. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS ltac:(vm_compute; reflexivity)). cbn [ss_pc].
apply K.
- exact HJ.
- exact HARU.
- exact SB1.
- assert (R2' : spZ (ms_regs ms) = spZ regs + - FRAME_pj_write) by exact R2.
  unfold FRAME_pj_write in *. lia.
- exact R1.
- exact R3.
- exact R4.
- exact R8.
- exact R9.
- apply bv_eq. etransitivity; [exact R10|]. unfold w64. rewrite unsigned_lit_small by lia. lia.
- exact R11.
- exact R12.
- exact Vs1.
- exact Vs0.
- exact Vra.
- exact Rs.
Qed.

(* ================= stage 2: the __asan_memset call (PC_memset 0x521bc, back at PJW_MS_RET 0x83d30) =================
   The 32 bytes of pj_out are set to 0. Premises: ecall_preU from the journal (FSW_K.fsw_ecall_preU_at), dest_ok
   from the journal's window presence and from ARU (the stack owns nothing), the two shadow premises from
   pjw_stack_shadow, and the written window [sp - 56, sp - 24) lies inside the journal's own stack window, which is
   what FSW_K.fsw_intrin_atU asks to put the journal back together. *)
Lemma pjw_memset_step :
  forall (W : world tfibsegs) ly S U regs mem md regs1 mem1 md1 (Q : world tfibsegs -> config -> Prop),
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly S W (unpoison U mem1) md1 0 ->
  ARU tfibsegs B ly S U W mem1 md1 ->
  spZ regs1 = spZ regs - FRAME_pj_write ->
  getr regs1 1 = w64 PJW_MS_RET ->
  getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
  getr regs1 10 = w64 (spZ regs - 56) -> getr regs1 11 = w64 0 -> getr regs1 12 = w64 32 ->
  (forall regs2 mem2 md2,
     ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
       ly S W (unpoison U mem2) md2 0 ->
     ARU tfibsegs B ly S U W mem2 md2 ->
     aregs_preserved regs1 regs2 ->
     (forall i, 0 <= i < 32 -> aview tfibsegs (w_H W) mem2 (spZ regs - 56 + i) = Some 0) ->
     (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 56 <= x < spZ regs - 24) ->
        ~ (spZ regs - FRAME_pj_write - ESTACK <= x < spZ regs - FRAME_pj_write) ->
        aview tfibsegs (w_H W) mem2 x = aview tfibsegs (w_H W) mem1 x) ->
     (forall x, apresent (w_H W) mem1 x -> apresent (w_H W) mem2 x) ->
     SRr tfibsegs W (cfg_at tfibsegs PJW_MS_RET regs2 mem2 md2) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs PC_memset regs1 mem1 md1) Q.
Proof.
intros W ly S U regs mem md regs1 mem1 md1 Q HJ HARU Hsp1 R1 R3 R4 R10 R11 R12 K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold FRAME_pj_write in *.
assert (HSTKv : 4160 <= STK_pj_write) by (vm_compute; discriminate).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HJ as (HARj & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hra : YK0s.ret_ok (getr regs1 1)).
{ apply YK0s.ret_ok_even. rewrite R1. unfold w64, PJW_MS_RET. rewrite unsigned_lit_small by lia. reflexivity. }
assert (HPREc : ecall_preU tfibsegs B ly S U W regs1 mem1 md1).
{ exact (fsw_ecall_preU_at B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md [] ly S U W mem1 md1 0
    regs1 (-64) HJ HARU ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) Hra R3 R4). }
assert (HDEST : dest_ok tfibsegs B ly S W regs1 mem1 (spZ regs - 56) 32).
{ intros x Hx. split; [|split].
  - apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly S U W mem1 md1 x HARU); [lia|]. apply Hpres. lia.
  - exact (ARU_stack tfibsegs B LAWS ly S U W mem1 md1 x HARU ltac:(lia)).
  - lia. }
destruct (pjw_stack_shadow W ly S U mem1 md1 (spZ regs - 56) 32 HARU ltac:(lia) ltac:(lia) ltac:(lia))
  as [HRA HHULL].
pose proof (RT_memset ly S U W regs1 mem1 md1 (spZ regs - 56) 0 32 HPREc R10 R11 R12
  ltac:(lia) ltac:(lia) ltac:(lia) HDEST ltac:(unfold amem_range; right; split; lia) HRA HHULL I) as HM.
eapply SRr_bind.
{ apply (fsw_intrin_atU B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md [] ly S U W mem1 md1 0
    U (fun x => (spZ regs - 56 <= x < spZ regs - 24) \/ (spZ regs - 64 - ESTACK <= x < spZ regs - 64))
    (getr regs1 1) (cfg_at tfibsegs PC_memset regs1 mem1 md1)
    (fun regs2 mem2 md2 =>
       aregs_preserved regs1 regs2 /\
       (forall i, 0 <= i < 32 -> aview tfibsegs (w_H W) mem2 (spZ regs - 56 + i) = Some 0) /\
       (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 56 <= x < spZ regs - 24) ->
          ~ (spZ regs - 64 - ESTACK <= x < spZ regs - 64) ->
          aview tfibsegs (w_H W) mem2 x = aview tfibsegs (w_H W) mem1 x) /\
       (forall x, apresent (w_H W) mem1 x -> apresent (w_H W) mem2 x))
    HJ).
  - (* the intrinsic's own post, in the kit step's shape (the journal reads the unpoisoned memories) *)
    eapply SRr_mono; [exact HM|]. cbv beta.
    intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc & HARU2 & HP2 & Hsame & H10' & Hset & Hfr & Hpr).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [rewrite Hc; unfold cfg_at, w64, raZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact HARU2|]. split; [exact Hsame|].
    split.
    { intros x Hx HnW.
      destruct (in_ush U (bv_unsigned (Z_to_bv 64 x))) eqn:Ei.
      - exact (aview_unpoison_in tfibsegs (w_H W) U mem2 mem1 x Ei).
      - rewrite (aview_unpoison_out tfibsegs (w_H W) U mem2 x Ei).
        rewrite (aview_unpoison_out tfibsegs (w_H W) U mem1 x Ei).
        apply Hfr; [lia | intros HH; apply HnW; left; lia | intros HH; apply HnW; right; lia]. }
    split.
    { intros x Hx.
      destruct (in_ush U (bv_unsigned (Z_to_bv 64 x))) eqn:Ei.
      - destruct Hx as [Hh _]. split; [exact Hh|]. exists (Z_to_bv 8 0). apply unpoison_in. exact Ei.
      - destruct Hx as [Hh [b Hb]]. rewrite (unpoison_out U mem1 _ Ei) in Hb.
        destruct (Hpr x (conj Hh (ex_intro _ b Hb))) as [Hh2 [b2 Hb2]].
        split; [exact Hh2|]. exists b2. rewrite (unpoison_out U mem2 _ Ei). exact Hb2. }
    split; [exact HP2|]. split; [exact Hset|]. split; [|exact Hpr].
    intros x Hx H1 H2. apply Hfr; [lia | intros HH; apply H1; lia | intros HH; apply H2; lia].
  - (* every byte the intrinsic may write is in the journal's own stack window *)
    intros x [Hx|Hx]; unfold awr_byte, awr_byte0; left; left; lia. }
cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & Hset & Hfr & Hpr).
rewrite R1.
apply K; assumption.
Qed.

(* a run of zero bytes, as the intrinsic's post gives them, is a zero value of any width *)
Lemma pjw_val_mem_zero : forall (W : world tfibsegs) (m : word -> option byte) a (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> aview tfibsegs (w_H W) m (a + i) = Some 0) ->
  val_mem tfibsegs (mrestrict (w_H W) m) a n 0.
Proof.
intros W m a n H k Hk.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (E : YO0f.le_byte 0 n k = 0)
  by (unfold YO0f.le_byte; rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia); rewrite Z.shiftr_0_l; reflexivity).
rewrite E.
destruct (aview_byte tfibsegs (w_H W) m (a + Z.of_nat k) 0 (H (Z.of_nat k) ltac:(lia)))
  as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite <- Hv. vm_compute. reflexivity.
Qed.

(* the resume state at PJW_MS_RET: the frame [sp - 64, sp) at the resumed sp (atom 2), holding the zeroed pj_out
   (offsets 8, 16, 24, 32) and the three saved registers (40 = s1, 48 = s0, 56 = ra) as the extra atoms 32, 33, 34
   of the env (FSW_K's atom convention for a NON-T state: the walk's extras start at atom 32) *)
Definition pjw_cs : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SLit 0));
   YP09.mkChunk 32 (CVal 4 (SLit 0));
   YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0)); YP09.mkChunk 56 (CVal 8 (SOff 32 0))].

(* ================= stage 3: the state at PJW_MS_RET, then the run 0x83d30 .. the write_value call 0x83d40 =========
   `addi a0, sp, 8` (= pj_out), `mv a1, s1` (v), `mv a2, s0` (pretty), `li a3, 0` (depth), `jal write_value`. *)
Lemma pjw_to_write_value :
  forall (W : world tfibsegs) ly S U regs mem md regs2 mem2 md2 (Q : world tfibsegs -> config -> Prop),
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly S W (unpoison U mem2) md2 0 ->
  ARU tfibsegs B ly S U W mem2 md2 ->
  spZ regs2 = spZ regs - FRAME_pj_write ->
  getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 11 -> getr regs2 9 = getr regs 10 ->
  (forall i, 0 <= i < 32 -> aview tfibsegs (w_H W) mem2 (spZ regs - 56 + i) = Some 0) ->
  val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs - 16) 8 (s0Z regs) ->
  val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs - 8) 8 (raZ regs) ->
  (forall regs3 mem3 md3,
     ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
       ly S W (unpoison U mem3) md3 0 ->
     ARU tfibsegs B ly S U W mem3 md3 ->
     spZ regs3 = spZ regs - FRAME_pj_write ->
     getr regs3 1 = w64 PJW_WV_RET ->
     getr regs3 3 = getr regs 3 -> getr regs3 4 = getr regs 4 ->
     getr regs3 8 = getr regs 11 -> getr regs3 9 = getr regs 10 ->
     getr regs3 10 = w64 (spZ regs - 56) ->
     getr regs3 11 = getr regs 10 -> getr regs3 12 = getr regs 11 -> getr regs3 13 = w64 0 ->
     val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 56) 8 0 ->
     val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 48) 8 0 ->
     val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 40) 8 0 ->
     val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 32) 4 0 ->
     val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
     val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 16) 8 (s0Z regs) ->
     val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 8) 8 (raZ regs) ->
     same_below mem2 mem3 alloc_ceiling ->
     aregs_preserved regs2 regs3 ->
     SRr tfibsegs W (cfg_at tfibsegs A_write_value regs3 mem3 md3) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs PJW_MS_RET regs2 mem2 md2) Q.
Proof.
intros W ly S U regs mem md regs2 mem2 md2 Q HJ HARU Hsp2 R3 R4 R8 R9 Hzero Vs1 Vs0 Vra K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold FRAME_pj_write in *.
assert (HSTKv : 4160 <= STK_pj_write) by (vm_compute; discriminate).
pose proof HJ as (HARj & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
set (extra := [getr regs 1; getr regs 8; getr regs 9]).
set (E := Ereg regs2 extra).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64)
  by (subst E; rewrite (ew_Ereg_nat regs2 extra 2 2%bv eq_refl); exact Hsp2).
assert (Z0 : val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs - 56) 8 0).
{ apply (pjw_val_mem_zero W mem2 (spZ regs - 56) 8). intros i Hi. apply Hzero. cbn [Z.of_nat] in Hi. lia. }
assert (Z1 : val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs - 48) 8 0).
{ apply (pjw_val_mem_zero W mem2 (spZ regs - 48) 8). intros i Hi.
  replace (spZ regs - 48 + i) with (spZ regs - 56 + (8 + i)) by lia. apply Hzero. cbn [Z.of_nat] in Hi. lia. }
assert (Z2 : val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs - 40) 8 0).
{ apply (pjw_val_mem_zero W mem2 (spZ regs - 40) 8). intros i Hi.
  replace (spZ regs - 40 + i) with (spZ regs - 56 + (16 + i)) by lia. apply Hzero. cbn [Z.of_nat] in Hi. lia. }
assert (Z3 : val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs - 32) 4 0).
{ apply (pjw_val_mem_zero W mem2 (spZ regs - 32) 4). intros i Hi.
  replace (spZ regs - 32 + i) with (spZ regs - 56 + (24 + i)) by lia. apply Hzero. cbn [Z.of_nat] in Hi. lia. }
assert (CHK : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem2) (spZ regs - 64)) pjw_cs).
{ unfold pjw_cs. repeat constructor.
  - apply (chunk_ok_val tfibsegs E _ (spZ regs - 64) 8 8%N (SLit 0) 0);
      [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
       | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; replace (spZ regs - 64 + 8) with (spZ regs - 56) by lia;
         exact Z0].
  - apply (chunk_ok_val tfibsegs E _ (spZ regs - 64) 16 8%N (SLit 0) 0);
      [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
       | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; replace (spZ regs - 64 + 16) with (spZ regs - 48) by lia;
         exact Z1].
  - apply (chunk_ok_val tfibsegs E _ (spZ regs - 64) 24 8%N (SLit 0) 0);
      [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
       | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; replace (spZ regs - 64 + 24) with (spZ regs - 40) by lia;
         exact Z2].
  - apply (chunk_ok_val tfibsegs E _ (spZ regs - 64) 32 4%N (SLit 0) 0);
      [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
       | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; replace (spZ regs - 64 + 32) with (spZ regs - 32) by lia;
         exact Z3].
  - apply (chunk_ok_val tfibsegs E _ (spZ regs - 64) 40 8%N (SOff 34 0) (bv_unsigned (getr regs 9))).
    + subst E. rewrite fsw_SOff0. change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra. cbn [nth extra].
      symmetry. apply Z_to_bv_bv_unsigned.
    + cbn [Z.of_N]. apply u64_range.
    + cbn [Z.of_N]; lia.
    + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. replace (spZ regs - 64 + 40) with (spZ regs - 24) by lia.
      exact Vs1.
  - apply (chunk_ok_val tfibsegs E _ (spZ regs - 64) 48 8%N (SOff 33 0) (s0Z regs)).
    + subst E. rewrite fsw_SOff0. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. cbn [nth extra].
      unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned.
    + cbn [Z.of_N]. unfold s0Z. apply u64_range.
    + cbn [Z.of_N]; lia.
    + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. replace (spZ regs - 64 + 48) with (spZ regs - 16) by lia.
      exact Vs0.
  - apply (chunk_ok_val tfibsegs E _ (spZ regs - 64) 56 8%N (SOff 32 0) (raZ regs)).
    + subst E. rewrite fsw_SOff0. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth extra].
      unfold raZ. symmetry. apply Z_to_bv_bv_unsigned.
    + cbn [Z.of_N]. unfold raZ. apply u64_range.
    + cbn [Z.of_N]; lia.
    + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. replace (spZ regs - 64 + 56) with (spZ regs - 8) by lia.
      exact Vra. }
pose proof (fsw_resume_after_rtU_chunks B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
  ly S U W mem2 md2 0 regs2 64 extra pjw_cs PJW_MS_RET HJ HARU ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(vm_compute; reflexivity) CHK) as HS.
fold E in HS.
unfold cfg_at. change (w64 PJW_MS_RET) with (Z_to_bv 64 PJW_MS_RET).
fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU A_write_value.
{ fsw_awr_ret Usp 64. }
pose proof (fsw_reg_lit (w_H W) E _ ms 1%bv PJW_WV_RET HS ltac:(vm_compute; reflexivity)
  ltac:(unfold PJW_WV_RET; lia)) as Q1.
pose proof (fsw_reg_off (w_H W) E _ ms 2%bv 2 0 (spZ regs - 64) HS ltac:(vm_compute; reflexivity) Usp
  ltac:(lia)) as Q2.
pose proof (fsw_reg_atom (w_H W) regs2 extra _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as Q3.
pose proof (fsw_reg_atom (w_H W) regs2 extra _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as Q4.
pose proof (fsw_reg_atom (w_H W) regs2 extra _ ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as Q8.
pose proof (fsw_reg_atom (w_H W) regs2 extra _ ms 9%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl) as Q9.
pose proof (fsw_reg_off (w_H W) E _ ms 10%bv 2 8 (spZ regs - 64) HS ltac:(vm_compute; reflexivity) Usp
  ltac:(lia)) as Q10.
pose proof (fsw_reg_atom (w_H W) regs2 extra _ ms 11%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl) as Q11.
pose proof (fsw_reg_atom (w_H W) regs2 extra _ ms 12%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as Q12.
pose proof (fsw_reg_lit (w_H W) E _ ms 13%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as Q13.
pose proof (fsw_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 8 8%N (SLit 0) 0 HR0 Usp ltac:(cbn; tauto)
  ltac:(reflexivity) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V0.
pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 16 8%N (SLit 0) 0 HR0 Usp ltac:(cbn; tauto)
  ltac:(reflexivity) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V1.
pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 24 8%N (SLit 0) 0 HR0 Usp ltac:(cbn; tauto)
  ltac:(reflexivity) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V2.
pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 32 4%N (SLit 0) 0 HR0 Usp ltac:(cbn; tauto)
  ltac:(reflexivity) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V3.
pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 40 8%N (SOff 34 0) (bv_unsigned (getr regs 9)) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(subst E; rewrite fsw_SOff0; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; cbn [nth extra];
        symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(cbn [Z.of_N]; apply u64_range) ltac:(cbn [Z.of_N]; lia)) as V4.
pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 48 8%N (SOff 33 0) (s0Z regs) HR0 Usp ltac:(cbn; tauto)
  ltac:(subst E; rewrite fsw_SOff0; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [nth extra];
        unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(cbn [Z.of_N]; unfold s0Z; apply u64_range) ltac:(cbn [Z.of_N]; lia)) as V5.
pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 56 8%N (SOff 32 0) (raZ regs) HR0 Usp ltac:(cbn; tauto)
  ltac:(subst E; rewrite fsw_SOff0; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; cbn [nth extra];
        unfold raZ; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(cbn [Z.of_N]; unfold raZ; apply u64_range) ltac:(cbn [Z.of_N]; lia)) as V6.
clear HR0.
pose proof (aregs_preserved_of_st_ok tfibsegs (w_H W) E _ ms regs2 extra HS ltac:(apply env_agree_refl)
  ltac:(vm_compute; reflexivity)) as HPRS0.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS ltac:(vm_compute; reflexivity)). cbn [ss_pc].
apply K.
- exact HJ.
- exact HARU.
- assert (Q2' : spZ (ms_regs ms) = spZ regs - 64 + 0) by exact Q2. lia.
- exact Q1.
- rewrite Q3. exact R3.
- rewrite Q4. exact R4.
- rewrite Q8. exact R8.
- rewrite Q9. exact R9.
- apply bv_eq. etransitivity; [exact Q10|]. unfold w64. rewrite unsigned_lit_small by lia. lia.
- rewrite Q11. exact R9.
- rewrite Q12. exact R8.
- exact Q13.
- replace (spZ regs - 56) with (spZ regs - 64 + 8) by lia. exact V0.
- replace (spZ regs - 48) with (spZ regs - 64 + 16) by lia. exact V1.
- replace (spZ regs - 40) with (spZ regs - 64 + 24) by lia. exact V2.
- replace (spZ regs - 32) with (spZ regs - 64 + 32) by lia. exact V3.
- replace (spZ regs - 24) with (spZ regs - 64 + 40) by lia. exact V4.
- replace (spZ regs - 16) with (spZ regs - 64 + 48) by lia. exact V5.
- replace (spZ regs - 8) with (spZ regs - 64 + 56) by lia. exact V6.
- (* the run to the call writes nothing below alloc_ceiling: its only region is the frame *)
  unfold fss_ret in HF. cbn [ss_mem] in HF.
  apply (same_below_frame1 E _ mem2 (ms_mem ms) alloc_ceiling HF);
    [cbn [YP09.r_base YP09.r_wlo base_val fstk_ret]; rewrite Usp; lia | lia].
- exact HPRS0.
Qed.

(* ================= stage 4: the premises of write_value at level 0, at the call site 0x83d40 =================
   Everything the callee's spec asks that is not already a premise of pj_write's own: its fpreU at the call (the
   core's afn_pre_at over the caller's journal, with the empty frame chain, since s0 holds `pretty` and pj_write's
   premise bounds it below alloc_ceiling), the zeroed `pj_out` as a wout_ok at buf = cap = failed = 0, text = [],
   the raised window top ot = sp - 16 (the first 16-aligned address above the object's end, FSH_Fn_FORM.md 3a), the
   window's presence, and that no node of the tree is the writer's buffer (buf = 0, every live block starts at
   4096 or above). *)
Lemma pjw_wv_premises :
  forall (W : world tfibsegs) ly S U regs mem md regs3 mem3 md3 (D UL : list (Z * Z)),
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly S W (unpoison U mem3) md3 0 ->
  ARU tfibsegs B ly S U W mem3 md3 ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem3) ->
  spZ regs3 = spZ regs - FRAME_pj_write ->
  getr regs3 1 = w64 PJW_WV_RET ->
  getr regs3 3 = w64 (as_gp B) -> getr regs3 4 = w64 (as_tp B) ->
  0 <= s0Z regs3 < alloc_ceiling ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 56) 8 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 48) 8 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 40) 8 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 32) 4 0 ->
  ublocks_ok B tfibsegs ly S W mem3 UL ->
  (forall a k, In (a, k) D -> In (a, k) UL) ->
  fpreU tfibsegs B (STK_write_value 2) ly S U W regs3 mem3 md3 [] /\
  wout_ok B tfibsegs ly S W mem3 (spZ regs - 56) 0 0 0 [] /\
  spZ regs3 <= spZ regs - 56 /\ spZ regs - 56 + 32 <= spZ regs - 16 /\
  (spZ regs - 16) mod 16 = 0 /\ spZ regs - 16 <= ly_top ly /\
  (forall a, spZ regs3 <= a < spZ regs - 16 -> apresent (w_H W) mem3 a) /\
  (forall a k, In (a, k) D -> In (a, k) UL /\ a <> 0) /\
  (* the callee's one-node frame chain at s0 = o (FSH_Fn_writer, a Theorem Labs lane's form): pj_write is case 1, the object
     sits right above the callee's frame and the return address into pj_write is an image address *)
  (spZ regs - 56 = spZ regs3 + 8 /\ raZ regs3 < alloc_ceiling).
Proof.
intros W ly S U regs mem md regs3 mem3 md3 D UL HJ HARU HRO Hsp3 Hra3 Hgp3 Htp3 Hpretty Z0 Z1 Z2 Z3 HUL HDUL.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold FRAME_pj_write in *.
assert (HSTKb : STK_write_value 2 + 64 <= STK_pj_write) by (vm_compute; discriminate).
assert (HSTK0 : 0 <= STK_write_value 2) by (vm_compute; discriminate).
assert (HSTKv : 4160 <= STK_pj_write) by (vm_compute; discriminate).
pose proof HJ as (HARj & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hpresent : forall a, spZ regs - 64 <= a < spZ regs - 16 -> apresent (w_H W) mem3 a).
{ intros a Ha. apply (fsw_apresent_unpoison B ly S U W mem3 md3 a HARU); [lia|]. apply Hpres. lia. }
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
- (* the callee's fpreU: the core's afn_pre_at at o = - 64, with the empty chain *)
  split; [|exact HRO]. split; [|split].
  + apply (afn_pre_at tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md [] ly S W
      (unpoison U mem3) md3 0 regs3 (STK_write_value 2) (-64) []).
    * exact HJ.
    * lia.
    * reflexivity.
    * lia.
    * exact HSTK0.
    * lia.
    * rewrite Hra3. apply YK0s.ret_ok_even. unfold w64, PJW_WV_RET. rewrite unsigned_lit_small by lia. reflexivity.
    * unfold raZ. rewrite Hra3. unfold w64, PJW_WV_RET. rewrite unsigned_lit_small by lia. lia.
    * exact Hgp3.
    * exact Htp3.
    * apply achain_low. lia.
  + exact (proj1 (proj2 HARU)).
  + exact (proj2 (proj2 HARU)).
- (* the zeroed object *)
  unfold wout_ok.
  split; [lia|]. split; [lia|]. split; [lia|].
  split.
  { intros i Hi. split; [apply (apresent_writable tfibsegs)|]; apply Hpresent; lia. }
  split; [lia|]. split; [lia|].
  split; [exact Z0|].
  split; [cbn [length]; replace (spZ regs - 56 + 8) with (spZ regs - 48) by lia; exact Z1|].
  split; [replace (spZ regs - 56 + 16) with (spZ regs - 40) by lia; exact Z2|].
  split; [replace (spZ regs - 56 + 24) with (spZ regs - 32) by lia; exact Z3|].
  split; [left; reflexivity|].
  split; [constructor|].
  left. split; [reflexivity|]. split; reflexivity.
- lia.
- lia.
- lia.
- lia.
- intros a Ha. apply Hpresent. lia.
- intros a k Hak. split; [exact (HDUL a k Hak)|].
  destruct (HUL a k (HDUL a k Hak)) as (Hin & Hal8 & Hk0 & _).
  destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem3) md3 (a - HEAD) (k + HEAD) HARj Hin)
    as (_ & H4096 & _).
  unfold HEAD in *. lia.
- split; [lia|]. unfold raZ. rewrite Hra3. unfold w64, PJW_WV_RET. rewrite unsigned_lit_small by lia. lia.
Qed.

(* ================= stage 6: the epilogue from PJW_PUT_RET 0x83d5c =================
   `ld a0, 8(sp)` (buf), `lw a1, 32(sp)` (failed), `beqz a1, 0x83d70`; at 0x83d70 the three reloads, `addi sp, sp,
   64`, `ret`. ONE resume shape serves every return from a writer callee and the epilogue: the object's three
   8-byte fields as the extra atoms 35 (buf), 36 (len), 37 (cap), its `failed` word as a LITERAL (so the engine
   decides the epilogue's branch itself), and the three saved registers as the atoms 32 (ra), 33 (s0), 34 (s1). *)
Definition pjw_cs_obj (failed : Z) : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (SOff 35 0)); YP09.mkChunk 16 (CVal 8 (SOff 36 0));
   YP09.mkChunk 24 (CVal 8 (SOff 37 0)); YP09.mkChunk 32 (CVal 4 (SLit failed));
   YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0)); YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
(* extra atoms 32 .. 37: the entry ra, s0, s1 (saved in the frame) and the object's buf, len, cap *)
Definition pjw_extra (regs : bvmap 5 word) (buf len cap : Z) : list word :=
  [getr regs 1; getr regs 8; getr regs 9; w64 buf; w64 len; w64 cap].
(* what each callee-saved register holds at the final ret, in the resume env *)
Definition pjw_expect (r : bv 5) : sv :=
  if Z.eqb (bv_unsigned r) 2 then SOff 2 64
  else if Z.eqb (bv_unsigned r) 8 then SOff 33 0
  else if Z.eqb (bv_unsigned r) 9 then SOff 34 0
  else SOff (Z.to_nat (bv_unsigned r)) 0.

(* the success arm: failed = 0, the function returns buf; fpostU's journal / ARU / registers through FSW_ret.fsw_retU,
   and the caller's Q from the memory below alloc_ceiling, which the epilogue does not write *)
Lemma pjw_epi_success :
  forall (W : world tfibsegs) ly S U regs mem md ly2 S2 U2 (W2 : world tfibsegs) regs2 mem2 md2 k2 buf len cap
    (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 mem2) md2 k2 ->
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 ->
  st_ok tfibsegs (Ereg regs2 (pjw_extra regs buf len cap)) (fss_ret PJW_PUT_RET 64 (pjw_cs_obj 0))
    (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 PJW_PUT_RET) mem2 (YK11.seg_rom tfibsegs))) ->
  spZ regs2 = spZ regs - 64 ->
  (forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 2 -> bv_unsigned q <> 8 ->
     bv_unsigned q <> 9 -> getr regs2 q = getr regs q) ->
  YK0s.ret_ok (getr regs 1) ->
  (forall regsF memF mdF, getr regsF 10 = w64 buf -> same_below mem2 memF alloc_ceiling ->
     Q ly2 S2 W2 regsF memF mdF) ->
  SRr tfibsegs W2 (cfg_at tfibsegs PJW_PUT_RET regs2 mem2 md2)
    (fpostU tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP regs ly S U W mem md k2 U2 Q).
Proof.
intros W ly S U regs mem md ly2 S2 U2 W2 regs2 mem2 md2 k2 buf len cap Q HJ HARU HS Hsp2 Hcs Hra HQ.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HARj & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTKv : 4160 <= STK_pj_write) by (vm_compute; discriminate).
set (E := Ereg regs2 (pjw_extra regs buf len cap)) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64)
  by (subst E; rewrite (ew_Ereg_nat regs2 (pjw_extra regs buf len cap) 2 2%bv eq_refl); exact Hsp2).
unfold cfg_at. change (w64 PJW_PUT_RET) with (Z_to_bv 64 PJW_PUT_RET).
fsw_aj_runU fsw_wr_tbl_ok HS HJ HARU.
{ fsw_awr_ret Usp 64. }
assert (SB : same_below mem2 (ms_mem ms) alloc_ceiling).
{ unfold fss_ret in HF. cbn [ss_mem] in HF.
  apply (same_below_frame1 E _ mem2 (ms_mem ms) alloc_ceiling HF);
    [cbn [YP09.r_base YP09.r_wlo base_val fstk_ret]; rewrite Usp; lia | lia]. }
pose proof (fsw_reg_extra (w_H W2) regs2 (pjw_extra regs buf len cap) _ ms 1%bv 0 HS
  ltac:(vm_compute; reflexivity)) as R1F.
pose proof (fsw_reg_extra (w_H W2) regs2 (pjw_extra regs buf len cap) _ ms 10%bv 3 HS
  ltac:(vm_compute; reflexivity))
  as R10F.
apply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok W2 E _ ms _ STK_pj_write (spZ regs) FS_PSTAT_FP regs ly S U W mem md
  ly2 S2 U2 k2 Q HS).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- rewrite R1F. cbn [nth pjw_extra]. exact Hra.
- exact HJ.
- exact HARU.
- apply (fsw_preserved (w_H W2) E _ ms regs pjw_expect HS); [vm_compute; reflexivity|].
  intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (pjw_expect ?q) = _ =>
    let e := eval vm_compute in (pjw_expect q) in change (pjw_expect q) with e end;
  try first
  [ exact (fsw_sp_back regs2 (pjw_extra regs buf len cap) regs 64 Usp)
  | rewrite fsw_SOff0; subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity
  | rewrite fsw_SOff0; subst E; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity ].
  (* s2 .. s11: kept by every call, read in the resume env as their own atoms *)
  all: rewrite fsw_SOff0; subst E.
  all: lazymatch goal with |- ew _ ?n = getr _ ?q => rewrite (ew_Ereg_nat _ _ n q eq_refl) end.
  all: apply Hcs; try (unfold acallee_saved);
       repeat match goal with |- context [bv_unsigned ?q] =>
         let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end;
       lia.
- intros mat2. apply HQ; [|exact SB]. rewrite R10F. reflexivity.
Qed.

(* ---- from FSW_pjw_model.v (a Theorem Labs lane), pasted unchanged ---- *)
(* Pure writer-model lemmas for pj_write's closing theorem (brief M). *)

Local Ltac pjw_m_proj :=
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].

Lemma pjw_putN_doc : forall cnt fail t p,
  WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p) =
  if p then WriterApp.put1 (WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wvpieces t p 0)) [10]
  else WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wvpieces t p 0).
Proof.
  intros cnt fail t p. unfold WriterValue.wdpieces. rewrite WriterApp.putN_app.
  destruct p; reflexivity.
Qed.

Lemma pjw_put1_fields : forall st b,
  let st2 := WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed st) (WriterApp.w_text st) (WriterApp.w_cap st)
               (WriterApp.w_cnt st) (WriterApp.w_fail st) []) b in
  WriterApp.w_failed st2 = WriterApp.w_failed (WriterApp.put1 st b) /\
  WriterApp.w_text st2 = WriterApp.w_text (WriterApp.put1 st b) /\
  WriterApp.w_cap st2 = WriterApp.w_cap (WriterApp.put1 st b) /\
  WriterApp.w_cnt st2 = WriterApp.w_cnt (WriterApp.put1 st b) /\
  WriterApp.w_fail st2 = WriterApp.w_fail (WriterApp.put1 st b).
Proof.
  intros [f t c n fl cs] b. unfold WriterApp.put1. pjw_m_proj.
  destruct (negb (f =? 0)); [pjw_m_proj; repeat split|].
  destruct (_ <=? c); [pjw_m_proj; repeat split|].
  destruct (n =? fl); pjw_m_proj; repeat split.
Qed.

Lemma pjw_put1_text : forall st b, WriterApp.w_failed (WriterApp.put1 st b) = 0 ->
  WriterApp.w_failed st = 0 /\ WriterApp.w_text (WriterApp.put1 st b) = WriterApp.w_text st ++ b.
Proof.
  intros [f t c n fl cs] b. unfold WriterApp.put1. pjw_m_proj.
  destruct (f =? 0) eqn:Ef; cbn [negb].
  - apply Z.eqb_eq in Ef.
    destruct (_ <=? c); [pjw_m_proj; intros _; split; [exact Ef|reflexivity]|].
    destruct (n =? fl); pjw_m_proj; [intros H; discriminate H|intros _; split; [exact Ef|reflexivity]].
  - apply Z.eqb_neq in Ef. pjw_m_proj. intros H. contradiction.
Qed.

Lemma pjw_putN_text : forall P st, WriterApp.w_failed (WriterApp.putN st P) = 0 ->
  WriterApp.w_failed st = 0 /\ WriterApp.w_text (WriterApp.putN st P) = WriterApp.w_text st ++ concat P.
Proof.
  induction P as [|b P IH]; intros st H.
  - rewrite WriterApp.putN_nil in *. split; [exact H|]. rewrite app_nil_r. reflexivity.
  - rewrite WriterApp.putN_cons in *. destruct (IH _ H) as [H1 H2].
    destruct (pjw_put1_text _ _ H1) as [H3 H4]. split; [exact H3|].
    rewrite H2, H4. cbn [concat]. rewrite app_assoc. reflexivity.
Qed.

Lemma pjw_put1_sticky : forall st b, WriterApp.w_failed st <> 0 -> WriterApp.put1 st b = st.
Proof.
  intros st b H. unfold WriterApp.put1.
  destruct (WriterApp.w_failed st =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|reflexivity].
Qed.

(* Brief M's lemma 6 (concat of the pieces is never empty) is false for a number node with empty text
   (WriterValue.v:19 writes the one piece []); a Theorem Labs lane replaced it by 6a / 6b below. *)

(* 6a: the list of pieces is never empty *)
Lemma pjw_wvpieces_cons : forall t p d, WriterValue.wvpieces t p d <> [].
Proof.
  intros [| | |txt bits|s|items|members] p d; cbn [WriterValue.wvpieces]; try unfold WriterSpec.spieces;
    discriminate.
Qed.

Lemma pjw_m_dbl_ge : forall f c need, 0 < c -> c <= WriterSpec.dbl f c need.
Proof.
  induction f as [|f IH]; intros c need Hc; cbn [WriterSpec.dbl]; [lia|].
  destruct (need <=? c); [lia|]. specialize (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma pjw_m_newcap_pos : forall c need, 0 <= c -> 0 < WriterSpec.newcap c need.
Proof.
  intros c need Hc. unfold WriterSpec.newcap.
  destruct (c =? 0) eqn:E.
  - pose proof (pjw_m_dbl_ge 64 4096 need ltac:(lia)). lia.
  - apply Z.eqb_neq in E. pose proof (pjw_m_dbl_ge 64 c need ltac:(lia)). lia.
Qed.

Lemma pjw_m_put1_cap_pos : forall st b, 0 < WriterApp.w_cap st -> 0 < WriterApp.w_cap (WriterApp.put1 st b).
Proof.
  intros [f t c n fl cs] b H. unfold WriterApp.put1. pjw_m_proj. cbn [WriterApp.w_cap] in H.
  destruct (negb (f =? 0)); [pjw_m_proj; exact H|].
  destruct (_ <=? c); [pjw_m_proj; exact H|].
  destruct (n =? fl); pjw_m_proj; [exact H|apply pjw_m_newcap_pos; lia].
Qed.

Lemma pjw_m_putN_cap_pos : forall P st, 0 < WriterApp.w_cap st -> 0 < WriterApp.w_cap (WriterApp.putN st P).
Proof.
  induction P as [|b P IH]; intros st H; [exact H|].
  rewrite WriterApp.putN_cons. apply IH. apply pjw_m_put1_cap_pos. exact H.
Qed.

(* 6b: once a nonempty piece list is put from w0 without failing, the buffer exists *)
Lemma pjw_putN_cap_pos : forall P cnt fail, P <> [] ->
  WriterApp.w_failed (WriterApp.putN (WriterApp.w0 cnt fail) P) = 0 ->
  WriterApp.w_cap (WriterApp.putN (WriterApp.w0 cnt fail) P) <> 0.
Proof.
  intros [|b P] cnt fail HP; [exfalso; exact (HP eq_refl)|].
  rewrite !WriterApp.putN_cons. unfold WriterApp.w0, WriterApp.put1. pjw_m_proj.
  cbn [negb Z.eqb].
  destruct (_ <=? 0) eqn:E; [apply Z.leb_le in E; lia|].
  destruct (cnt =? fail).
  - rewrite WriterApp.putN_failed by (pjw_m_proj; discriminate).
    pjw_m_proj. intros H; discriminate H.
  - intros _.
    match goal with |- WriterApp.w_cap (WriterApp.putN ?s P) <> 0 =>
      assert (Hp : 0 < WriterApp.w_cap (WriterApp.putN s P)) end; [|lia].
    apply pjw_m_putN_cap_pos. pjw_m_proj. apply pjw_m_newcap_pos. lia.
Qed.

Lemma pjw_wdoc_split : forall t p,
  WriterValue.wdoc t p = concat (WriterValue.wvpieces t p 0) ++ (if p then [10] else []).
Proof.
  intros t p. unfold WriterValue.wdoc, WriterValue.wdpieces. rewrite concat_app.
  destruct p; cbn [concat app]; reflexivity.
Qed.

Lemma pjw_wbud_range : forall f c, 0 <= c <= WMAX -> (c = 0 \/ exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j) ->
  0 <= wbud f c <= WGROWS_MAX + 1.
Proof.
  intros f c Hc Hp. unfold wbud, WGROWS_MAX, wgrows. unfold WMAX in Hc.
  change (2 ^ 27) with 134217728 in Hc.
  destruct (f =? 0); [|lia].
  destruct Hp as [-> | [j [Hj ->]]]; [cbn; lia|].
  assert (Hpos : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (Hj15 : j <= 15).
  { destruct (Z.le_gt_cases j 15) as [Hle|Hg]; [exact Hle|exfalso].
    assert (H16 : 2 ^ 16 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 16) with 65536 in H16. lia. }
  destruct (4096 * 2 ^ j =? 0) eqn:E; [apply Z.eqb_eq in E; lia|].
  rewrite Z.mul_comm, Z.div_mul by lia. rewrite Z.log2_pow2 by lia. lia.
Qed.

Lemma pjw_wbud00 : wbud 0 0 = WGROWS_MAX + 1.
Proof. reflexivity. Qed.

Lemma pjw_app_last : forall (X : Type) (A X1 X2 : list X) (b : X), ~ In b A -> A ++ [b] = X1 ++ b :: X2 ->
  X1 = A /\ X2 = [].
Proof.
  intros X A. induction A as [|a A IH]; intros X1 X2 b Hn E.
  - destruct X1 as [|x X1]; cbn [app] in E.
    + apply (f_equal (@tl X)) in E. cbn [tl] in E. split; [reflexivity|symmetry; exact E].
    + injection E as Ex E2. exfalso. destruct X1; discriminate E2.
  - destruct X1 as [|x X1]; cbn [app] in E.
    + injection E as Ea _. subst a. exfalso. apply Hn. left. reflexivity.
    + injection E as Ex E2. subst x.
      destruct (IH X1 X2 b (fun h => Hn (or_intror h)) E2) as [H1 H2].
      rewrite H1, H2. split; reflexivity.
Qed.

Lemma pjw_put1_failed01 : forall st b, (WriterApp.w_failed st = 0 \/ WriterApp.w_failed st = 1) ->
  WriterApp.w_failed (WriterApp.put1 st b) = 0 \/ WriterApp.w_failed (WriterApp.put1 st b) = 1.
Proof.
  intros [f t c n fl cs] b H. unfold WriterApp.put1.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls] in *.
  destruct (negb (f =? 0)); [pjw_m_proj; exact H|].
  destruct (_ <=? c); [pjw_m_proj; left; reflexivity|].
  destruct (n =? fl); pjw_m_proj; [right|left]; reflexivity.
Qed.

(* ---- from FSW_pjw_tr.v (a Theorem Labs lane), pasted unchanged ---- *)

Definition pjw_avb (W : world tfibsegs) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.

(* ---- helpers ---- *)
(* a restricted byte below alloc_ceiling and off the image: aview equality is raw (restricted) equality *)
Lemma pjw_t_mrZ : forall (W : world tfibsegs) m m' a, pjw_avb W m m' -> 0 <= a < alloc_ceiling ->
  ~ in_img tfibsegs a -> mrestrict (w_H W) m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a).
Proof.
intros W m m' a Hv Ha Hn. pose proof alloc_ceiling_lt as Hc.
pose proof (mbyte_of_aview tfibsegs (w_H W) (w_H W) m m' a (Hv a Ha)) as X. unfold mbyte in X.
rewrite (seg_rom_none tfibsegs a ltac:(lia) Hn) in X.
destruct (mrestrict (w_H W) m' (Z_to_bv 64 a)), (mrestrict (w_H W) m (Z_to_bv 64 a)); congruence.
Qed.
Lemma pjw_t_mr : forall (W : world tfibsegs) m m' (x : word), pjw_avb W m m' -> bv_unsigned x < alloc_ceiling ->
  ~ in_img tfibsegs (bv_unsigned x) -> mrestrict (w_H W) m' x = mrestrict (w_H W) m x.
Proof.
intros W m m' x Hv Hx Hn. pose proof (u64_range x) as Hr.
assert (E : x = Z_to_bv 64 (bv_unsigned x)) by (symmetry; apply Z_to_bv_bv_unsigned).
rewrite E. apply pjw_t_mrZ; [exact Hv | lia | exact Hn].
Qed.
Lemma pjw_t_val_mem : forall (W : world tfibsegs) m m' a (n : nat) v, pjw_avb W m m' ->
  0 <= a -> a + Z.of_nat n <= alloc_ceiling ->
  val_mem tfibsegs (mrestrict (w_H W) m) a n v -> val_mem tfibsegs (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v Hv H0 Hn Hm k Hk.
rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) m m' (a + Z.of_nat k)); [exact (Hm k Hk)|].
apply Hv. lia.
Qed.
Lemma pjw_t_range_addressable : forall (W : world tfibsegs) m m' p n, pjw_avb W m m' ->
  0 <= p -> p + n <= alloc_ceiling ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF p n ->
  range_addressable (aview tfibsegs (w_H W) m') SHADOW_OFF p n.
Proof.
intros W m m' p n Hv Hp Hn Hr x Hx. destruct (Hr x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
assert (Hx' : 0 <= x < alloc_ceiling) by lia.
rewrite (Hv _ (fsw_shadow_below x Hx')). exact Es.
Qed.
(* the root node's 56 bytes are off the image (a live fake frame or a live heap block) *)
Lemma pjw_t_pobj_img : forall ly S (W : world tfibsegs) mx md m v, AR tfibsegs B ly S W mx md ->
  FSH_Fn_reader.pobj tfibsegs B ly S W m v -> forall a, v <= a < v + 56 -> ~ in_img tfibsegs a.
Proof.
intros ly S W mx md m v HAR HP a Ha. pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct HP as ([((cid & pos & Hin & Hc & _ & H1 & H2) & _)|((b & n & Hin & H1 & H2) & _)] & _).
- apply (frm_img tfibsegs B LAWS ly S W mx md cid pos a HAR Hin). lia.
- apply (blk_img tfibsegs B LAWS ly S W mx md b n a HAR Hin). unfold HEAD in *. lia.
Qed.
(* every block of a node's list is one of lblk's (pj_node states lblk of each entry it adds) *)
Lemma pjw_t_items_in : forall (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (R : Z * Z -> Prop) l a D,
  (forall a' u D1, In u l -> P a' u D1 -> forall b, In b D1 -> R b) ->
  PjStruct.pj_items P a l D -> forall b, In b D -> R b.
Proof.
intros P R l. induction l as [|u r IH]; intros a D H Hl b Hb; cbn [PjStruct.pj_items] in Hl.
- subst D. destruct Hb.
- destruct Hl as (D1 & D2 & E & HP & HR). subst D. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
  + exact (H a u D1 (or_introl eq_refl) HP b Hb).
  + apply (IH (a + 56) D2); [|exact HR | exact Hb].
    intros a' u' D3 Hu HP3 b' Hb'. exact (H a' u' D3 (or_intror Hu) HP3 b' Hb').
Qed.
Lemma pjw_t_mems_in : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (R : Z * Z -> Prop) l a ka D,
  (forall a' nm u D1, In (nm, u) l -> P a' u D1 -> forall b, In b D1 -> R b) ->
  (forall x k, lblk x k -> R (x, k)) ->
  PjStruct.pj_mems tfibsegs m lblk P a ka l D -> forall b, In b D -> R b.
Proof.
intros m lblk P R l. induction l as [|[nm u] r IH]; intros a ka D H HL Hl b Hb; cbn [PjStruct.pj_mems] in Hl.
- subst D. destruct Hb.
- destruct Hl as (x & k & D1 & D2 & E & _ & Hc & HP & HR). subst D. destruct Hb as [Hb|Hb].
  + subst b. apply HL. exact (proj1 Hc).
  + apply in_app_or in Hb. destruct Hb as [Hb|Hb].
    * exact (H a nm u D1 (or_introl eq_refl) HP b Hb).
    * apply (IH (a + 56) (ka + 8) D2); [| exact HL | exact HR | exact Hb].
      intros a' nm' u' D3 Hu HP3 b' Hb'. exact (H a' nm' u' D3 (or_intror Hu) HP3 b' Hb').
Qed.
Lemma pjw_t_node_lblk : forall t m lblk p D, PjStruct.pj_node tfibsegs m lblk p t D ->
  forall b, In b D -> lblk (fst b) (snd b).
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk p D H b Hb; cbn [PjStruct.pj_node] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & Hd).
- destruct Hd as (_ & _ & _ & _ & _ & ED). subst D. destruct Hb.
- destruct Hd as (_ & _ & _ & _ & _ & ED). subst D. destruct Hb.
- destruct Hd as (_ & _ & _ & _ & _ & ED). subst D. destruct Hb.
- destruct Hd as (_ & _ & _ & _ & _ & k & Hc & ED). subst D. destruct Hb as [Hb|[]]. subst b. exact (proj1 Hc).
- destruct Hd as (_ & _ & _ & _ & k & Hc & ED). subst D. destruct Hb as [Hb|[]]. subst b. exact (proj1 Hc).
- destruct Hd as (_ & _ & _ & _ & Hcap & Di & ED & Hi). subst D. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
  + destruct (cap =? 0) eqn:Ec; [destruct Hb|]. apply Z.eqb_neq in Ec.
    destruct Hb as [Hb|[]]. subst b. cbn [fst snd].
    destruct Hcap as [(Hc0 & _)|(_ & L)]; [lia | exact L].
  + apply (pjw_t_items_in (PjStruct.pj_node tfibsegs m lblk) (fun b => lblk (fst b) (snd b)) items kids Di);
      [| exact Hi | exact Hb].
    intros a' u D1 Hu HP b' Hb'. rewrite Forall_forall in IH. exact (IH u Hu m lblk a' D1 HP b' Hb').
- destruct Hd as (_ & _ & _ & Hcap & Di & ED & Hi). subst D. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
  + destruct (cap =? 0) eqn:Ec; [destruct Hb|]. apply Z.eqb_neq in Ec.
    destruct Hcap as [(Hc0 & _)|(_ & L0 & L1)]; [lia|].
    destruct Hb as [Hb|[Hb|[]]]; subst b; cbn [fst snd]; assumption.
  + apply (pjw_t_mems_in m lblk (PjStruct.pj_node tfibsegs m lblk) (fun b => lblk (fst b) (snd b))
      members kids keys Di); [| | exact Hi | exact Hb].
    * intros a' nm u D1 Hu HP b' Hb'. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
      exact (IH m lblk a' D1 HP b' Hb').
    * intros x k Hx. exact Hx.
Qed.

(* ---- the eight transports ---- *)
Lemma pjw_avb_of_same_below : forall W m m', same_below m m' alloc_ceiling -> pjw_avb W m m'.
Proof. intros W m m' Hs a Ha. exact (aview_below (w_H W) m m' alloc_ceiling a Hs Ha). Qed.

Lemma pjw_avb_trans : forall W m1 m2 m3, pjw_avb W m1 m2 -> pjw_avb W m2 m3 -> pjw_avb W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

Lemma pjw_fs_glob_avb : forall W m m' live peak cnt fail, pjw_avb W m m' ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hv (G1 & G2 & G3 & G4 & R).
pose proof asan_consts as (C1 & _).
assert (VB : forall a v, 0 <= a -> a + 8 <= alloc_ceiling -> val_mem tfibsegs (mrestrict (w_H W) m) a 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) m') a 8 v).
{ intros a v Ha Hb Hm. exact (pjw_t_val_mem W m m' a 8 v Hv Ha Hb Hm). }
unfold fs_glob, fs_glob_at. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VB; [lia | lia | exact G1]|].
split; [apply VB; [lia | lia | exact G2]|].
split; [apply VB; [lia | lia | exact G3]|].
split; [apply VB; [lia | lia | exact G4]|].
exact R.
Qed.

Lemma pjw_arodata_avb : forall W m m', pjw_avb W m m' ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m').
Proof.
intros W m m' Hv HR a Ha Ho He. pose proof asan_consts as (C1 & _).
assert (Hb : 0 <= a < alloc_ceiling).
{ destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; lia].
  assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
  pose proof (fs_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl. lia. }
rewrite (Hv a Hb). exact (HR a Ha Ho He).
Qed.

Lemma pjw_rblock_avb : forall ly S W m m' mx md p n, AR tfibsegs B ly S W mx md -> pjw_avb W m m' ->
  fs_rblock tfibsegs B ly S W m p n -> fs_rblock tfibsegs B ly S W m' p n.
Proof.
intros ly S W m m' mx md p n HAR Hv Hb. pose proof Hb as (Hin & Hal & Hn & Hm).
destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin) as (A1 & A2 & A3).
split; [exact Hin|]. split; [exact Hal|]. split; [exact Hn|].
apply (pjw_t_val_mem W m m' (p - HEAD) 8 n Hv); [unfold HEAD in *; lia | | exact Hm].
change (Z.of_nat 8) with 8. unfold HEAD in *. lia.
Qed.

Lemma pjw_ublocks_avb : forall ly S W m m' mx md UL, AR tfibsegs B ly S W mx md -> pjw_avb W m m' ->
  ublocks_ok B tfibsegs ly S W m UL -> ublocks_ok B tfibsegs ly S W m' UL.
Proof.
intros ly S W m m' mx md UL HAR Hv H a k Hak. exact (pjw_rblock_avb ly S W m m' mx md a k HAR Hv (H a k Hak)).
Qed.

Lemma pjw_pobj_avb : forall ly S W m m' mx md v, AR tfibsegs B ly S W mx md -> pjw_avb W m m' ->
  FSH_Fn_reader.pobj tfibsegs B ly S W m v -> FSH_Fn_reader.pobj tfibsegs B ly S W m' v.
Proof.
intros ly S W m m' mx md v HAR Hv HP.
destruct (fsw_pobj_low B ly S W mx md m v HAR HP) as (L1 & L2).
pose proof (pjw_t_pobj_img ly S W mx md m v HAR HP) as HNI.
destruct HP as [Hpl Hw]. split.
- destruct Hpl as [(Hf & Ha & Hr)|(Hb & Ha & Hr)]; [left | right].
  + split; [exact Hf|]. split; [exact Ha|].
    exact (pjw_t_range_addressable W m m' v 56 Hv ltac:(lia) L2 Hr).
  + split; [exact Hb|]. split; [exact Ha|].
    exact (pjw_t_range_addressable W m m' v 56 Hv ltac:(lia) L2 Hr).
- intros i Hi. apply (writable_at_eq tfibsegs (mrestrict (w_H W) m) (mrestrict (w_H W) m') (v + i)); [|exact (Hw i Hi)].
  apply pjw_t_mrZ; [exact Hv | lia | apply HNI; lia].
Qed.

Lemma pjw_pj_node_avb : forall ly S W m m' mx md lblk v t D UL, AR tfibsegs B ly S W mx md -> pjw_avb W m m' ->
  FSH_Fn_reader.pobj tfibsegs B ly S W m v -> ublocks_ok B tfibsegs ly S W m UL ->
  (forall a k, In (a, k) D -> In (a, k) UL) ->
  PjStruct.pj_node tfibsegs (mrestrict (w_H W) m) lblk v t D ->
  PjStruct.pj_node tfibsegs (mrestrict (w_H W) m') lblk v t D.
Proof.
intros ly S W m m' mx md lblk v t D UL HAR Hv HP HU HD HN.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
apply (PjStruct.pj_node_frame tfibsegs t (mrestrict (w_H W) m) lblk (mrestrict (w_H W) m') lblk v D HN).
- intros a k Hak. exact (pjw_t_node_lblk t (mrestrict (w_H W) m) lblk v D HN (a, k) Hak).
- intros x Hx. apply (pjw_t_mr W m m' x Hv).
  + destruct Hx as [Hx|((a & k) & Hb & Hx)].
    * destruct (fsw_pobj_low B ly S W mx md m v HAR HP) as (L1 & L2). lia.
    * destruct (HU a k (HD a k Hb)) as (Hin & _ & _ & _).
      destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin) as (A1 & A2 & A3).
      unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx. unfold HEAD in *. lia.
  + destruct Hx as [Hx|((a & k) & Hb & Hx)].
    * exact (pjw_t_pobj_img ly S W mx md m v HAR HP _ Hx).
    * destruct (HU a k (HD a k Hb)) as (Hin & _ & _ & _).
      destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin) as (A1 & A2 & A3).
      unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx.
      apply (blk_img tfibsegs B LAWS ly S W mx md (a - HEAD) (k + HEAD) (bv_unsigned x) HAR Hin).
      unfold HEAD in *. lia.
Qed.

(* ---- from FSW_pjw_jr.v (a Theorem Labs lane), pasted unchanged ---- *)

(* ---- every block of a node's list satisfies the node's block relation ---- *)
Lemma pjw_j_items_lblk : forall (lblk : Z -> Z -> Prop) (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D,
  Forall (fun u => forall a' D', P a' u D' -> forall x k, In (x, k) D' -> lblk x k) l ->
  PjStruct.pj_items P a l D -> forall x k, In (x, k) D -> lblk x k.
Proof.
intros lblk P l. induction l as [|u r IH]; intros a D HF Hl x k Hin; cbn [PjStruct.pj_items] in Hl.
- subst D. destruct Hin.
- destruct Hl as (D1 & D2 & -> & HP & HR). apply Forall_cons_iff in HF as [Hu HF].
  apply in_app_or in Hin as [Hin|Hin]; [exact (Hu _ _ HP x k Hin) | exact (IH (a + 56) D2 HF HR x k Hin)].
Qed.
Lemma pjw_j_mems_lblk : forall m (lblk : Z -> Z -> Prop) (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  Forall (fun nu : list Z * PjTree.jv => forall a' D', P a' (snd nu) D' -> forall x k, In (x, k) D' -> lblk x k) l ->
  PjStruct.pj_mems tfibsegs m lblk P a ka l D -> forall x k, In (x, k) D -> lblk x k.
Proof.
intros m lblk P l. induction l as [|[nm u] r IH]; intros a ka D HF Hl x k Hin; cbn [PjStruct.pj_mems] in Hl.
- subst D. destruct Hin.
- destruct Hl as (x0 & k0 & D1 & D2 & -> & _ & (Hlb & _ & _) & HP & HR). apply Forall_cons_iff in HF as [Hu HF].
  destruct Hin as [E|Hin]; [injection E as <- <-; exact Hlb|].
  apply in_app_or in Hin as [Hin|Hin]; [exact (Hu _ _ HP x k Hin) | exact (IH (a + 56) (ka + 8) D2 HF HR x k Hin)].
Qed.
Lemma pjw_j_node_lblk : forall t m lblk p D, PjStruct.pj_node tfibsegs m lblk p t D ->
  forall a k, In (a, k) D -> lblk a k.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk p D H a k Hin; cbn [PjStruct.pj_node] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & Hb).
- destruct Hb as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct Hb as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct Hb as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct Hb as (_ & _ & _ & _ & _ & k0 & (Hl & _) & ->). destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
- destruct Hb as (_ & _ & _ & _ & k0 & (Hl & _) & ->). destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
- destruct Hb as (_ & _ & _ & _ & Hcap & Di & -> & Hi).
  apply in_app_or in Hin as [Hin|Hin].
  + revert Hin. destruct (Z.eqb_spec cap 0) as [E0|E0]; [intros []|]. intros [E|[]]. injection E as <- <-.
    destruct Hcap as [(Hc & _)|(_ & Hl)]; [lia | exact Hl].
  + apply (pjw_j_items_lblk lblk (PjStruct.pj_node tfibsegs m lblk) items kids Di); [|exact Hi|exact Hin].
    eapply Forall_impl; [|exact IH]. intros u Hu a' D' HP x k' Hx. exact (Hu m lblk a' D' HP x k' Hx).
- destruct Hb as (_ & _ & _ & Hcap & Di & -> & Hi).
  apply in_app_or in Hin as [Hin|Hin].
  + revert Hin. destruct (Z.eqb_spec cap 0) as [E0|E0]; [intros []|].
    destruct Hcap as [(Hc & _)|(_ & Hl1 & Hl2)]; [lia|].
    intros [E|[E|[]]]; injection E as <- <-; assumption.
  + apply (pjw_j_mems_lblk m lblk (PjStruct.pj_node tfibsegs m lblk) members kids keys Di); [|exact Hi|exact Hin].
    eapply Forall_impl; [|exact IH]. intros nu Hu a' D' HP x k' Hx. exact (Hu m lblk a' D' HP x k' Hx).
Qed.

(* ---- an app byte of a block or a frame is never a user-poisoned shadow byte ---- *)
Lemma pjw_j_app_not_ush : forall ly S U (W : world tfibsegs) m md a lo len, ARU tfibsegs B ly S U W m md ->
  in_app lo len -> lo <= a < lo + len -> in_ush U (bv_unsigned (Z_to_bv 64 a)) = false.
Proof.
intros ly S U W m md a lo len HARU Happ Ha.
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E; [|reflexivity]. exfalso.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in *; lia).
rewrite (wz _ Ha64) in E.
destruct (ush_facts tfibsegs B ly S U W m md a HARU E) as (_ & L1 & L2).
unfold in_app, kLowShadowBeg, SHADOW_OFF, ASAN_CEIL in *. lia.
Qed.

(* ---- an app byte off the image whose unpoisoned view is kept is kept on the machine's own memories ---- *)
Lemma pjw_j_view_kept : forall ly S U (W : world tfibsegs) m md ly' S' U' (W' : world tfibsegs) m' md' a lo len,
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  in_app lo len -> lo <= a < lo + len -> ~ in_img tfibsegs a ->
  aview tfibsegs (w_H W') (unpoison U' m') a = aview tfibsegs (w_H W) (unpoison U m) a ->
  aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a /\
  mrestrict (w_H W') m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a).
Proof.
intros ly S U W m md ly' S' U' W' m' md' a lo len HARU HARU' Happ Ha Hni E.
rewrite (aview_unpoison_out tfibsegs _ U' m' a (pjw_j_app_not_ush ly' S' U' W' m' md' a lo len HARU' Happ Ha)) in E.
rewrite (aview_unpoison_out tfibsegs _ U m a (pjw_j_app_not_ush ly S U W m md a lo len HARU Happ Ha)) in E.
split; [exact E|].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in *; lia).
pose proof (mbyte_of_aview tfibsegs _ _ _ _ a E) as Em.
pose proof (seg_rom_none tfibsegs a Ha64 Hni) as Hr.
unfold mbyte in Em. rewrite Hr in Em.
destruct (mrestrict (w_H W') m' (Z_to_bv 64 a)), (mrestrict (w_H W) m (Z_to_bv 64 a)); congruence.
Qed.

(* ---- a byte of a block live at both ends, outside FP, is kept ---- *)
Lemma pjw_j_blk_kept : forall STK sp0 FP ly S U (W : world tfibsegs) m md own ly' S' U' (W' : world tfibsegs) m' md' k p n a,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> p <= a < p + req_size n -> ~ inFP FP a ->
  aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a /\
  mrestrict (w_H W') m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a).
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k p n a HJ HARU HARU' H1 H2 Ha Hnf.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (proj1 HARU) as HAR.
destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U m) md p n HAR H1) as (_ & _ & _ & Happ & _).
apply (pjw_j_view_kept ly S U W m md ly' S' U' W' m' md' a p (req_size n) HARU HARU' Happ Ha).
- exact (blk_img tfibsegs B LAWS ly S W (unpoison U m) md p n a HAR H1 Ha).
- pose proof (F2 p n (a - p) H1 H2 ltac:(lia) ltac:(replace (p + (a - p)) with a by lia; exact Hnf)) as E.
  replace (p + (a - p)) with a in E by lia. exact E.
Qed.

(* ---- a byte of a frame of frames S, outside FP, is kept ---- *)
Lemma pjw_j_frm_kept : forall STK sp0 FP ly S U (W : world tfibsegs) m md own ly' S' U' (W' : world tfibsegs) m' md' k
  cid pos a,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  In (cid, pos) (frames S) -> frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
  ~ inFP FP a ->
  aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a /\
  mrestrict (w_H W') m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a).
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k cid pos a HJ HARU HARU' Hin Ha Hnf.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
pose proof (proj1 HARU) as HAR.
destruct (al_frames tfibsegs B LAWS ly S W (unpoison U m) md cid pos HAR Hin) as (_ & Happ & _).
apply (pjw_j_view_kept ly S U W m md ly' S' U' W' m' md' a _ _ HARU HARU' Happ Ha).
- exact (frm_img tfibsegs B LAWS ly S W (unpoison U m) md cid pos a HAR Hin Ha).
- apply (F4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hnf].
Qed.

(* ---- every byte of the tree's footprint is kept ---- *)
Lemma pjw_j_foot_kept : forall STK sp0 FP ly S U (W : world tfibsegs) m md own ly' S' U' (W' : world tfibsegs) m' md' k
  v D UL a,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  FSH_Fn_reader.pobj tfibsegs B ly S W m v -> ublocks_ok B tfibsegs ly S W m UL ->
  (forall a kk, In (a, kk) D -> In (a, kk) UL) ->
  (forall b n x, In (b, n) (ablocks B ly S) -> b <= x < b + req_size n -> PjStruct.pj_foot v D x ->
     In (b, n) (ablocks B ly' S')) ->
  (forall x, PjStruct.pj_foot v D x -> ~ inFP FP x) ->
  PjStruct.pj_foot v D a ->
  aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a /\
  mrestrict (w_H W') m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a).
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k v D UL a HJ HARU HARU' HP HUL HD HLIVE HFP Hf.
pose proof (HFP a Hf) as Hnf. pose proof Hf as Hf0.
destruct Hf as [Hv | ((a0 & kk) & Hb & Hx)].
- destruct HP as ([((cid & pos & Hin & Hc & Hal & H1 & H2) & _ & _) | ((b & mm & Hin & H1 & H2) & _ & _)] & _).
  + exact (pjw_j_frm_kept STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k cid pos a HJ HARU HARU' Hin
      ltac:(lia) Hnf).
  + assert (Hba : b <= a < b + req_size mm) by (unfold HEAD in *; lia).
    exact (pjw_j_blk_kept STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k b mm a HJ HARU HARU' Hin
      (HLIVE b mm a Hin Hba Hf0) Hba Hnf).
- unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx.
  destruct (HUL a0 kk (HD a0 kk Hb)) as (Hin & _ & Hk & _).
  pose proof (req_size_pos (kk + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr).
  assert (Hba : a0 - HEAD <= a < a0 - HEAD + req_size (kk + HEAD)) by (unfold HEAD in *; lia).
  exact (pjw_j_blk_kept STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k (a0 - HEAD) (kk + HEAD) a HJ HARU HARU'
    Hin (HLIVE _ _ a Hin Hba Hf0) Hba Hnf).
Qed.

(* ================= 1. the tree across the journal ================= *)
Lemma pjw_pj_node_journal : forall STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k lblk v t D UL,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  FSH_Fn_reader.pobj tfibsegs B ly S W m v -> ublocks_ok B tfibsegs ly S W m UL ->
  (forall a kk, In (a, kk) D -> In (a, kk) UL) ->
  (forall b n x, In (b, n) (ablocks B ly S) -> b <= x < b + req_size n -> PjStruct.pj_foot v D x ->
     In (b, n) (ablocks B ly' S')) ->
  (forall x, PjStruct.pj_foot v D x -> ~ inFP FP x) ->
  PjStruct.pj_node tfibsegs (mrestrict (w_H W) m) lblk v t D ->
  PjStruct.pj_node tfibsegs (mrestrict (w_H W') m') lblk v t D.
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k lblk v t D UL HJ HARU HARU' HP HUL HD HLIVE HFP HN.
apply (PjStruct.pj_node_frame tfibsegs t (mrestrict (w_H W) m) lblk (mrestrict (w_H W') m') lblk v D HN).
- exact (pjw_j_node_lblk t _ lblk v D HN).
- intros x Hx.
  pose proof (proj2 (pjw_j_foot_kept STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k v D UL (bv_unsigned x)
    HJ HARU HARU' HP HUL HD HLIVE HFP Hx)) as E.
  rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

(* ================= 2. the root object across the journal =================
   The same premises as 1 (the root's block, when it is one, stays live: the liveness premise covers every byte of
   pj_foot v D, the root's 56 bytes included; a root frame stays live because frames S' = own ++ frames S), plus two
   facts about SHADOW bytes, which no journal clause keeps for a block and clause F4 keeps for a frame only off FP:
   - fs_heads at the end: every user-poisoned range of U' is the 16-byte head at the start of a live block, so none
     covers the root's 56 bytes (a root in a block lies past its head; any other block is disjoint), hence the raw
     shadow reads as AR's (YCbq.range_addressable_of_block);
   - FP misses the shadow region (YCbq.range_addressable_entry_frame's premise form), for a root in a frame. *)
Lemma pjw_pobj_journal : forall STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k v D UL,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  FSH_Fn_reader.pobj tfibsegs B ly S W m v -> ublocks_ok B tfibsegs ly S W m UL ->
  (forall a kk, In (a, kk) D -> In (a, kk) UL) ->
  (forall b n x, In (b, n) (ablocks B ly S) -> b <= x < b + req_size n -> PjStruct.pj_foot v D x ->
     In (b, n) (ablocks B ly' S')) ->
  (forall x, PjStruct.pj_foot v D x -> ~ inFP FP x) ->
  fs_heads B ly' S' U' ->
  (forall x, inFP FP x -> x < kLowShadowBeg \/ kHighShadowEnd <= x) ->
  FSH_Fn_reader.pobj tfibsegs B ly' S' W' m' v.
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k v D UL HJ HARU HARU' HP HUL HD HLIVE HFP HH HFPS.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
pose proof (proj1 HARU) as HAR. pose proof (proj1 HARU') as HAR'.
assert (Hkept : forall i, 0 <= i < 56 ->
  mrestrict (w_H W') m' (Z_to_bv 64 (v + i)) = mrestrict (w_H W) m (Z_to_bv 64 (v + i))).
{ intros i Hi. refine (proj2 (pjw_j_foot_kept STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k v D UL (v + i)
    HJ HARU HARU' HP HUL HD HLIVE HFP _)). left. lia. }
pose proof HP as [Hpl Hw]. split.
2: { intros i Hi. apply (writable_at_eq tfibsegs (mrestrict (w_H W) m)); [exact (Hkept i Hi) | exact (Hw i Hi)]. }
destruct Hpl as [((cid & pos & Hin & Hc & Hal & H1 & H2) & Hv8 & Hra) | ((b & mm & Hin & H1 & H2) & Hv8 & Hra)].
- (* a root in a live fake frame *)
  left.
  assert (Efa : frame_addr ly' cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U m) md cid pos HAR Hin) as (Hf0 & Hfc & _).
  split; [exists cid, pos; rewrite Efa; repeat split; assumption|].
  split; [exact Hv8|].
  (* the frame's shadow bytes are no block's, at either end, so unpoison does not touch them *)
  assert (NB : forall ly0 S0 U0 (W0 : world tfibsegs) m0 md0 x, ARU tfibsegs B ly0 S0 U0 W0 m0 md0 ->
    In (cid, pos) (frames S0) -> frame_addr ly0 cid pos = frame_addr ly cid pos -> v <= x < v + 56 ->
    aview tfibsegs (w_H W0) m0 (shadow_of_addr SHADOW_OFF x) =
    aview tfibsegs (w_H W0) (unpoison U0 m0) (shadow_of_addr SHADOW_OFF x)).
  { intros ly0 S0 U0 W0 m0 md0 x HARU0 Hin0 Efa0 Hx. symmetry. apply aview_unpoison_out.
    change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
    apply (ARU_shadow_out_block tfibsegs B ly0 S0 U0 W0 m0 md0 x HARU0); [unfold ASAN_CEIL in *; lia|].
    intros p n Hpn Hpx.
    pose proof (sep_block_frame tfibsegs B LAWS ly0 S0 W0 (unpoison U0 m0) md0 p n cid pos (proj1 HARU0) Hpn Hin0)
      as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efa0 in Hd. lia. }
  apply (range_addressable_agree (aview tfibsegs (w_H W') (unpoison U' m'))).
  { intros x Hx. exact (NB ly' S' U' W' m' md' x HARU' Hin' Efa Hx). }
  apply (range_addressable_entry_frame tfibsegs B LAWS STK sp0 FP ly S W (unpoison U m) md own ly' S' W'
    (unpoison U' m') md' k cid pos v 56 HJ Hin Hc H1 H2 Hal HFPS HAR).
  apply (range_addressable_agree (aview tfibsegs (w_H W) m)); [|exact Hra].
  intros x Hx. symmetry. exact (NB ly S U W m md x HARU Hin eq_refl Hx).
- (* a root in a live heap block, past its head *)
  right.
  assert (Hba : forall x, v <= x < v + 56 -> b <= x < b + req_size mm) by (intros x Hx; unfold HEAD in *; lia).
  assert (Hin' : In (b, mm) (ablocks B ly' S')).
  { apply (HLIVE b mm v Hin (Hba v ltac:(lia))). left. lia. }
  split; [exists b, mm; split; [exact Hin'|]; split; assumption|].
  split; [exact Hv8|].
  apply (range_addressable_agree (aview tfibsegs (w_H W') (unpoison U' m'))).
  2: { exact (range_addressable_of_block tfibsegs B LAWS ly' S' W' (unpoison U' m') md' b mm v 56 HAR' Hin'
         ltac:(unfold HEAD in *; lia) H2). }
  intros x Hx. symmetry. apply aview_unpoison_out.
  destruct (in_ush U' (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x)))) eqn:E; [|reflexivity]. exfalso.
  destruct (al_blocks tfibsegs B LAWS ly' S' W' (unpoison U' m') md' b mm HAR' Hin') as (_ & Hb4 & Hbc & _).
  assert (Hx0 : 0 <= x < alloc_ceiling) by (pose proof (Hba x Hx); lia).
  assert (Hs64 : 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64).
  { unfold shadow_of_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound x 8 (2 ^ 61) ltac:(lia) ltac:(lia)). lia. }
  rewrite (wz _ Hs64) in E.
  apply in_ush_spec in E as (r & Hr & Hs).
  destruct (HH r Hr) as (Hsn & m0 & Hb0 & Hq0).
  rewrite Hsn in Hs. replace (16 / 8) with 2 in Hs by reflexivity.
  destruct (al_blocks tfibsegs B LAWS ly' S' W' (unpoison U' m') md' (fst r) m0 HAR' Hb0) as (Hr16 & _).
  assert (Hrx : fst r <= x < fst r + 16).
  { unfold shadow_addr, shadow_of_addr in Hs.
    pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
    pose proof (Z.div_mod (fst r) 8 ltac:(lia)) as Dr. pose proof (Z.mod_pos_bound (fst r) 8 ltac:(lia)) as Mr.
    assert (Er : fst r mod 8 = 0).
    { apply Z.mod_divide in Hr16 as [q Hq]; [|lia]. rewrite Hq. replace (q * 16) with ((2 * q) * 8) by lia.
      apply Z_mod_mult. }
    lia. }
  destruct (Z.eq_dec (fst r) b) as [Eb|Eb].
  + unfold HEAD in *. lia.
  + assert (Ne : (fst r, m0) <> (b, mm)) by (intros Eq; injection Eq as E1 E2; exact (Eb E1)).
    pose proof (sep_blocks tfibsegs B LAWS ly' S' W' (unpoison U' m') md' (fst r) m0 b mm HAR' Hb0 Hin' Ne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (Hba x Hx). lia.
Qed.

(* ================= 3. the live list across the journal ================= *)
Lemma pjw_ublocks_journal : forall STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k UL,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  ublocks_ok B tfibsegs ly S W m UL ->
  (forall a kk, In (a, kk) UL -> In (a - HEAD, kk + HEAD) (ablocks B ly' S')) ->
  (forall a kk i, In (a, kk) UL -> 0 <= i < 8 -> ~ inFP FP (a - HEAD + i)) ->
  ublocks_ok B tfibsegs ly' S' W' m' UL.
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k UL HJ HARU HARU' HUL HLIVE HFP a kk Hak.
destruct (HUL a kk Hak) as (Hin & Hal & Hk & Hv).
split; [exact (HLIVE a kk Hak)|]. split; [exact Hal|]. split; [exact Hk|].
intros j Hj. rewrite <- (Hv j Hj).
pose proof (req_size_pos (kk + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr).
destruct (pjw_j_blk_kept STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k (a - HEAD) (kk + HEAD)
  (a - HEAD + Z.of_nat j) HJ HARU HARU' Hin (HLIVE a kk Hak) ltac:(unfold HEAD in *; lia)
  (HFP a kk (Z.of_nat j) Hak ltac:(lia))) as (_ & E).
unfold mbyte. rewrite E. reflexivity.
Qed.

(* ---- the read-only range is image bytes, all below SHADOW_OFF ---- *)
Lemma pjw_j_roP_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
assert (Hb : existsb (fun s => (Z.of_N (seg_base s) <=? FS_RLO) && (FS_RHI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (s & Hs & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.
(* below SHADOW_OFF the raw memory is the unpoisoned one *)
Lemma pjw_j_mrestrict_low : forall ly S U (W : world tfibsegs) m md (H : word -> bool) x,
  ARU tfibsegs B ly S U W m md -> 0 <= x < SHADOW_OFF ->
  mrestrict H (unpoison U m) (Z_to_bv 64 x) = mrestrict H m (Z_to_bv 64 x).
Proof.
intros ly S U W m md H x HARU Hx. unfold mrestrict. destruct (H (Z_to_bv 64 x)); [reflexivity|].
apply (ARU_mem_low tfibsegs B ly S U W m md _ HARU). rewrite wz by (unfold SHADOW_OFF in *; lia). lia.
Qed.
(* arodata over the raw memory and over the unpoisoned one are the same fact under ARU *)
Lemma pjw_j_arodata_unpoison : forall ly S U (W : world tfibsegs) m md, ARU tfibsegs B ly S U W m md ->
  (arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) <->
   arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U m))).
Proof.
intros ly S U W m md HARU.
assert (E : forall a, in_roP tfibsegs FS_RLO FS_RHI a ->
  aview tfibsegs (w_H W) (unpoison U m) a = aview tfibsegs (w_H W) m a).
{ intros a Hro. pose proof (fs_segs_img a (pjw_j_roP_img a Hro)) as Hl.
  unfold aview, mbyte. rewrite (pjw_j_mrestrict_low ly S U W m md (w_H W) a HARU)
    by (unfold FS_IMG_END, SHADOW_OFF in *; lia).
  reflexivity. }
split; intros H a Hro Ho He; [rewrite (E a Hro) | rewrite <- (E a Hro)]; exact (H a Hro Ho He).
Qed.

(* ================= 4. the "\n" literal at any ARU state with arodata =================
   The arodata premise is over the UNPOISONED memory (the form fs_img_facts takes); pjw_j_arodata_unpoison turns the
   raw-memory form (fpreU's) into it. *)
Lemma pjw_ro_lit_kept : forall ly S U W m md, ARU tfibsegs B ly S U W m md ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U m)) ->
  fs_img_facts tfibsegs B -> In (0x21040, [10]) FS_RO_STRS -> zbytes_at tfibsegs W m 0x21040 [10].
Proof.
intros ly S U W m md HARU HRO HIMG Hin.
unfold fs_img_facts, fs_img_facts_at in HIMG. destruct HIMG as (_ & HI).
destruct (HI ly S W (unpoison U m) md (proj1 HARU) HRO) as (_ & _ & HS & _).
pose proof (proj1 (Forall_forall _ _) HS _ Hin) as (((Hg & _) & _) & _).
intros j Hj. destruct j as [|j]; [|cbn in Hj; lia].
destruct (Hg 0%nat ltac:(cbn; lia)) as (Hv & Hb). split; [|exact Hb].
intros kk Hkk. etransitivity; [|exact (Hv kk Hkk)].
assert (Hkk0 : kk = 0%nat) by lia. subst kk.
unfold mbyte. rewrite (pjw_j_mrestrict_low ly S U W m md (w_H W)) by (exact HARU || (unfold SHADOW_OFF; cbn; lia)).
reflexivity.
Qed.

(* ================= 5. arodata across the journal =================
   No existing lemma has this core's form: A/ACeg.v arodata_ok_journal is stated over the donor's in_ro_tfa / YCe5
   journal. This core's image clause (YCbq.v:361-362) keeps an image byte that is not runtime-owned, not errno and
   fp_spares FP; the read-only range is image bytes (pjw_j_roP_img), so the premise is fp_spares FP over it (a caller
   with ~ YI16.sink_open_fp FP, e.g. every FP whose ranges start above 0 (YCbq.sink_closed_pos), has it by
   YCbq.fp_spares_closed). Stated over the journal's own memories, then in the walk's raw-memory form. *)
(* FP-keyed core (S0 400b2a240b3): the image clause spares an image byte that is not runtime-owned, not errno,
   NOT in FP and fp_spares FP, so the caller states both FP premises over the read-only range. *)
Lemma pjw_arodata_journal : forall STK sp0 FP ly S (W : world tfibsegs) mem md own ly' S' (W' : world tfibsegs) mem' md' k,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FP a) ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> fp_spares FP a) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HNFP HFP HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a (pjw_j_roP_img a Hro) Ho He (HNFP a Hro) (HFP a Hro)). exact (HR a Hro Ho He).
Qed.
Lemma pjw_j_arodata_journalU : forall STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FP a) ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> fp_spares FP a) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') m').
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k HJ HARU HARU' HNFP HFP HR.
apply (proj2 (pjw_j_arodata_unpoison ly' S' U' W' m' md' HARU')).
apply (pjw_arodata_journal STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k HJ HNFP HFP).
exact (proj1 (pjw_j_arodata_unpoison ly S U W m md HARU) HR).
Qed.

(* ================= the walk's own data premises, carried from the entry to the write_value call ===============
   Stages 1 to 3 change memory only in pj_write's frame: stage 1 and stage 3 keep every byte below alloc_ceiling
   (same_below), stage 2's __asan_memset keeps every shadow-view byte outside [sp - 56, sp - 24) and outside the
   runtime's own ESTACK window, both of which lie above alloc_ceiling. So the view below alloc_ceiling is the
   entry's, and every data premise of pj_write's spec rides across on `pjw_avb`. *)
Lemma pjw_avb_entry_to_call : forall (W : world tfibsegs) (regs : bvmap 5 word) mem mem1 mem2 mem3,
  alloc_ceiling + STK_pj_write <= spZ regs ->
  same_below mem mem1 alloc_ceiling ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 56 <= x < spZ regs - 24) ->
     ~ (spZ regs - FRAME_pj_write - ESTACK <= x < spZ regs - FRAME_pj_write) ->
     aview tfibsegs (w_H W) mem2 x = aview tfibsegs (w_H W) mem1 x) ->
  same_below mem2 mem3 alloc_ceiling ->
  pjw_avb W mem mem3.
Proof.
intros W regs mem mem1 mem2 mem3 Hceil SB1 FR2 SB3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold FRAME_pj_write in *.
assert (HSTKv : 4160 <= STK_pj_write) by (vm_compute; discriminate).
assert (HES : ESTACK = 4096) by reflexivity.
apply (pjw_avb_trans W mem mem2 mem3); [|exact (pjw_avb_of_same_below W mem2 mem3 SB3)].
apply (pjw_avb_trans W mem mem1 mem2); [exact (pjw_avb_of_same_below W mem mem1 SB1)|].
intros a Ha. apply FR2; [lia | intros HH; lia | intros HH; lia].
Qed.

(* ================= stage 5b: the branch on `pretty` at PJW_WV_RET, and the put of the final newline =========
   (proved by a part agent of a Theorem Labs lane in its scratch workspace, folded unchanged) *)

(* the branch condition the engine adds is not part of the resume shape: only `conds_ok E [] = True` changes
   (donor, same tree: lib/A/AE2y.v:604-609 st_ok_dropc / DROPC; YP0l.v:102-111 st_ok, YP0m.v:473-484 facts_ok) *)
Lemma pjw_p_st_ok_nocond : forall E ss ms, st_ok tfibsegs E ss ms ->
  st_ok tfibsegs E (set_facts ss (mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss)))) ms.
Proof.
intros E ss ms HS. eapply st_ok_set_facts; [exact HS|].
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (HA & _ & HL)).
split; [exact HA|]. split; [exact I | exact HL].
Qed.

(* a state whose register file is still the entry atoms holds the entry registers *)
Lemma pjw_p_regs_eq : forall (H : word -> bool) regs0 extra ss ms,
  st_ok tfibsegs (Ereg regs0 extra) ss (restrict H ms) ->
  ss_regs ss = sr_atoms -> forall r : bv 5, getr (ms_regs ms) r = getr regs0 r.
Proof.
intros H regs0 extra ss ms HS Hr r.
destruct HS as (_ & _ & _ & _ & _ & _ & HR & _ & _).
rewrite Hr in HR.
transitivity (sv_denot (Ereg regs0 extra) (sr_get sr_atoms r)); [exact (HR r)|].
symmetry. exact (regs_ok_Ereg regs0 extra r).
Qed.

(* then the resume env may be read at those registers *)
Lemma pjw_p_env_regs : forall k regs0 regsX extra, (forall r : bv 5, getr regsX r = getr regs0 r) ->
  env_agree k (Ereg regs0 extra) (Ereg regsX extra).
Proof.
intros k regs0 regsX extra H. split; [|reflexivity].
intros n Hn. unfold Ereg. cbn [ew]. destruct (n <? 32)%nat; [apply H | reflexivity].
Qed.

(* ---- 1. pretty = 0: `beqz s0, PJW_PUT_RET` is taken and nothing else happens ---- *)
Lemma pjw_pretty0_to_epi : forall (W : world tfibsegs) ly S U regs mem md ly2 S2 U2 (W2 : world tfibsegs)
  regs2 mem2 md2 k2 buf len cap failed (Q : world tfibsegs -> config -> Prop),
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 mem2) md2 k2 ->
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 ->
  st_ok tfibsegs (Ereg regs2 (pjw_extra regs buf len cap)) (fss_ret PJW_WV_RET 64 (pjw_cs_obj failed))
    (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 PJW_WV_RET) mem2 (YK11.seg_rom tfibsegs))) ->
  spZ regs2 = spZ regs - FRAME_pj_write -> getr regs2 8 = w64 0 -> (failed = 0 \/ failed = 1) ->
  (forall regsE memE mdE,
     ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
       ly2 S2 W2 (unpoison U2 memE) mdE k2 ->
     ARU tfibsegs B ly2 S2 U2 W2 memE mdE ->
     st_ok tfibsegs (Ereg regsE (pjw_extra regs buf len cap)) (fss_ret PJW_PUT_RET 64 (pjw_cs_obj failed))
       (restrict (w_H W2) (YK11.mkst regsE (Z_to_bv 64 PJW_PUT_RET) memE (YK11.seg_rom tfibsegs))) ->
     spZ regsE = spZ regs - FRAME_pj_write ->
     (forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regsE q = getr regs2 q) ->
     same_below mem2 memE alloc_ceiling ->
     SRr tfibsegs W2 (cfg_at tfibsegs PJW_PUT_RET regsE memE mdE) Q) ->
  SRr tfibsegs W2 (cfg_at tfibsegs PJW_WV_RET regs2 mem2 md2) Q.
Proof.
intros W ly S U regs mem md ly2 S2 U2 W2 regs2 mem2 md2 k2 buf len cap failed Q HJ HARU HS Hsp2 H8 Hf01 K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold FRAME_pj_write in Hsp2.
assert (HSTKv : 4160 <= STK_pj_write) by (vm_compute; discriminate).
set (E := Ereg regs2 (pjw_extra regs buf len cap)) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64)
  by (subst E; rewrite (ew_Ereg_nat regs2 (pjw_extra regs buf len cap) 2 2%bv eq_refl); exact Hsp2).
assert (E8 : ew E 8 = Z_to_bv 64 0)
  by (subst E; rewrite (ew_Ereg_nat regs2 (pjw_extra regs buf len cap) 8 8%bv eq_refl); exact H8).
unfold cfg_at. change (w64 PJW_WV_RET) with (Z_to_bv 64 PJW_WV_RET).
srr_branch_with fsw_wr_tbl_ok HS.
- (* taken: one step to PJW_PUT_RET, nothing written *)
  fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU PJW_PUT_RET.
  { fsw_awr_ret Usp 64. }
  assert (SB : same_below mem2 (ms_mem ms) alloc_ceiling).
  { unfold fss_ret in HF. cbn [add_cond ss_mem] in HF.
    apply (same_below_frame1 E _ mem2 (ms_mem ms) alloc_ceiling HF);
      [cbn [YP09.r_base YP09.r_wlo base_val fstk_ret]; rewrite Usp; lia | lia]. }
  pose proof (pjw_p_regs_eq (w_H W2) regs2 (pjw_extra regs buf len cap) _ ms HS
    ltac:(vm_compute; reflexivity)) as HRG.
  pose proof (pjw_p_st_ok_nocond E _ _ HS) as HSn.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) E _ ms HS ltac:(vm_compute; reflexivity)) in HSn.
  cbn [ss_pc] in HSn.
  assert (HSE : st_ok tfibsegs (Ereg (ms_regs ms) (pjw_extra regs buf len cap))
      (fss_ret PJW_PUT_RET 64 (pjw_cs_obj failed))
      (restrict (w_H W2) (YK11.mkst (ms_regs ms) (Z_to_bv 64 PJW_PUT_RET) (ms_mem ms) (YK11.seg_rom tfibsegs)))).
  { eapply st_ok_agree;
      [ exact HSn | apply (pjw_p_env_regs 38 regs2 (ms_regs ms)); exact HRG | vm_compute; reflexivity ]. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) E _ ms HS ltac:(vm_compute; reflexivity)). cbn [ss_pc].
  apply K.
  + exact HJ.
  + exact HARU.
  + exact HSE.
  + unfold spZ, FRAME_pj_write. rewrite (HRG 2%bv). exact Hsp2.
  + intros q _. exact (HRG q).
  + exact SB.
- (* not taken: impossible, s0 = 0 *)
  exfalso. rewrite branch_eq_U in Hc.
  rewrite (U_atom E 8 0 E8 ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hc.
  discriminate Hc.
Qed.

(* ================= stage 7: the FAILED arm (failed = 1 at PJW_PUT_RET): fuzz_free (buf), return NULL ==========
   Drafted by a part agent of a Theorem Labs lane (scratch, at the 04:45Z pause), finished and built here. Premises beyond the
   brief: gp / tp at entry (fsw_fpreU_atFP's), and for _block that the freed block was not live at pj_write's
   entry (fsw_fp_sub's in_tmp_block arm). fuzz_free's window top is its own sp, so the kit's plain
   FSW_K3.fsw_after_callFPU carries the saved words across the call. *)

Local Ltac pjw_f_bvz :=
  repeat match goal with |- context [bv_unsigned ?q] =>
    let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end.

(* the resume shape after fuzz_free: the three saved words only (the epilogue reads nothing else) *)
Definition pjw_f_cs : list YP09.chunk :=
  [YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0)); YP09.mkChunk 56 (CVal 8 (SOff 32 0))].

Lemma pjw_f_cs_in : Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 64) pjw_f_cs.
Proof.
apply Forall_forall. intros c Hc. cbv [pjw_f_cs In] in Hc.
repeat (destruct Hc as [<-|Hc]; [cbn; lia|]). destruct Hc.
Qed.

(* fuzz/alloc.c's statics are image bytes *)
Lemma pjw_f_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a ([lo hi] & Hr & Ha). cbn [fst snd] in Ha.
assert (Hb : existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true).
{ cbv [FS_PSTAT_FP In] in Hr.
  repeat (destruct Hr as [Hr|Hr]; [injection Hr as <- <-; vm_compute; reflexivity|]). destruct Hr. }
apply existsb_exists in Hb as (s & Hs & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.

(* a head that overlaps itself sits at one place only in a pairwise-disjoint list *)
Lemma pjw_f_split_uniq : forall (x : Z * Z) U1 U2 V1 V2, pairwise zdisjoint (U1 ++ x :: U2) -> ~ zdisjoint x x ->
  U1 ++ x :: U2 = V1 ++ x :: V2 -> U1 = V1 /\ U2 = V2.
Proof.
intros x U1. induction U1 as [|u U1 IH]; intros U2 V1 V2 HP Hx E; destruct V1 as [|v V1]; cbn [app] in *.
- injection E as E. split; [reflexivity | exact E].
- injection E as E1 E2. subst v. exfalso. apply Hx. destruct HP as [HF _]. rewrite Forall_forall in HF.
  apply HF. rewrite E2. apply in_or_app. right. left. reflexivity.
- injection E as E1 E2. subst u. exfalso. apply Hx. destruct HP as [HF _]. rewrite Forall_forall in HF.
  apply HF. apply in_or_app. right. left. reflexivity.
- injection E as E1 E2. subst v. destruct HP as [_ HP].
  destruct (IH U2 V1 V2 HP Hx E2) as [-> ->]. split; reflexivity.
Qed.

(* the run PJW_PUT_RET .. `jal fuzz_free` with failed = 1 (the literal decides the branch) *)
Lemma pjw_f_to_call :
  forall (W : world tfibsegs) ly S U regs mem md ly2 S2 U2 (W2 : world tfibsegs) regs2 mem2 md2 k2 buf len cap
    (Q : world tfibsegs -> config -> Prop),
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 mem2) md2 k2 ->
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 ->
  st_ok tfibsegs (Ereg regs2 (pjw_extra regs buf len cap)) (fss_ret PJW_PUT_RET 64 (pjw_cs_obj 1))
    (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 PJW_PUT_RET) mem2 (YK11.seg_rom tfibsegs))) ->
  spZ regs2 = spZ regs - 64 ->
  (forall regsc memc mdc,
     ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
       ly2 S2 W2 (unpoison U2 memc) mdc k2 ->
     ARU tfibsegs B ly2 S2 U2 W2 memc mdc ->
     same_below mem2 memc alloc_ceiling ->
     spZ regsc = spZ regs - 64 ->
     getr regsc 1 = w64 PJW_FREE_RET -> getr regsc 10 = w64 buf ->
     aregs_preserved regs2 regsc ->
     (forall regs', Forall (YP09.chunk_ok tfibsegs (Ereg regs' (pjw_extra regs buf len cap))
        (mrestrict (w_H W2) memc) (spZ regs - 64)) pjw_f_cs) ->
     SRr tfibsegs W2 (cfg_at tfibsegs A_fuzz_free regsc memc mdc) Q) ->
  SRr tfibsegs W2 (cfg_at tfibsegs PJW_PUT_RET regs2 mem2 md2) Q.
Proof.
intros W ly S U regs mem md ly2 S2 U2 W2 regs2 mem2 md2 k2 buf len cap Q HJ HARU HS Hsp2 K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTKv : 4160 <= STK_pj_write) by (vm_compute; discriminate).
set (E := Ereg regs2 (pjw_extra regs buf len cap)) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64)
  by (subst E; rewrite (ew_Ereg_nat regs2 (pjw_extra regs buf len cap) 2 2%bv eq_refl); exact Hsp2).
unfold cfg_at. change (w64 PJW_PUT_RET) with (Z_to_bv 64 PJW_PUT_RET).
fsw_aj_runU fsw_wr_tbl_ok HS HJ HARU.
{ fsw_awr_ret Usp 64. }
assert (SB : same_below mem2 (ms_mem ms) alloc_ceiling).
{ unfold fss_ret in HF. cbn [ss_mem] in HF.
  apply (same_below_frame1 E _ mem2 (ms_mem ms) alloc_ceiling HF);
    [cbn [YP09.r_base YP09.r_wlo base_val fstk_ret]; rewrite Usp; lia | lia]. }
pose proof (fsw_reg_lit (w_H W2) E _ ms 1%bv PJW_FREE_RET HS ltac:(vm_compute; reflexivity)
  ltac:(unfold PJW_FREE_RET; lia)) as R1.
pose proof (fsw_reg_off (w_H W2) E _ ms 2%bv 2 0 (spZ regs - 64) HS ltac:(vm_compute; reflexivity) Usp
  ltac:(lia)) as R2.
pose proof (fsw_reg_extra (w_H W2) regs2 (pjw_extra regs buf len cap) _ ms 10%bv 3 HS
  ltac:(vm_compute; reflexivity)) as R10.
assert (HPc : aregs_preserved regs2 (ms_regs ms)).
{ exact (aregs_preserved_of_st_ok tfibsegs (w_H W2) E _ ms regs2 (pjw_extra regs buf len cap) HS
    ltac:(split; [intros; reflexivity | reflexivity]) ltac:(vm_compute; reflexivity)). }
pose proof (fsw_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 40 8%N (SOff 34 0) (bv_unsigned (getr regs 9)) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(subst E; rewrite fsw_SOff0; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; cbn [nth pjw_extra];
        symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(cbn [Z.of_N]; apply u64_range) ltac:(cbn [Z.of_N]; lia)) as V4.
pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 48 8%N (SOff 33 0) (bv_unsigned (getr regs 8)) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(subst E; rewrite fsw_SOff0; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [nth pjw_extra];
        symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(cbn [Z.of_N]; apply u64_range) ltac:(cbn [Z.of_N]; lia)) as V5.
pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 56 8%N (SOff 32 0) (bv_unsigned (getr regs 1)) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(subst E; rewrite fsw_SOff0; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; cbn [nth pjw_extra];
        symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(cbn [Z.of_N]; apply u64_range) ltac:(cbn [Z.of_N]; lia)) as V6.
clear HR0.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) E _ ms HS ltac:(vm_compute; reflexivity)). cbn [ss_pc].
apply K.
- exact HJ.
- exact HARU.
- exact SB.
- assert (R2' : spZ (ms_regs ms) = spZ regs - 64 + 0) by exact R2. lia.
- exact R1.
- rewrite R10. reflexivity.
- exact HPc.
- intros regs'. unfold pjw_f_cs.
  constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 40 8%N (SOff 34 0) (bv_unsigned (getr regs 9))).
    * rewrite fsw_SOff0. change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
      symmetry. apply Z_to_bv_bv_unsigned.
    * cbn [Z.of_N]. apply u64_range.
    * cbn [Z.of_N]. lia.
    * exact V4.
  + apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 48 8%N (SOff 33 0) (bv_unsigned (getr regs 8))).
    * rewrite fsw_SOff0. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
      symmetry. apply Z_to_bv_bv_unsigned.
    * cbn [Z.of_N]. apply u64_range.
    * cbn [Z.of_N]. lia.
    * exact V5.
  + apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 56 8%N (SOff 32 0) (bv_unsigned (getr regs 1))).
    * rewrite fsw_SOff0. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
      symmetry. apply Z_to_bv_bv_unsigned.
    * cbn [Z.of_N]. apply u64_range.
    * cbn [Z.of_N]. lia.
    * exact V6.
Qed.

(* fuzz_free's fpreU at the call (sp = entry sp - 64, ra = PJW_FREE_RET, s0 = pretty below alloc_ceiling) *)
Lemma pjw_f_fpre :
  forall (W : world tfibsegs) ly S U regs mem md ly2 S2 U2 (W2 : world tfibsegs) regs2 regsc memc mdc k2,
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 memc) mdc k2 ->
  ARU tfibsegs B ly2 S2 U2 W2 memc mdc ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) memc) ->
  spZ regsc = spZ regs - 64 -> getr regsc 1 = w64 PJW_FREE_RET -> aregs_preserved regs2 regsc ->
  (forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 2 -> bv_unsigned q <> 8 ->
     bv_unsigned q <> 9 -> getr regs2 q = getr regs q) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  0 <= s0Z regs2 < alloc_ceiling ->
  fpreU tfibsegs B STK_fuzz_free ly2 S2 U2 W2 regsc memc mdc [] /\ raZ regsc = PJW_FREE_RET.
Proof.
intros W ly S U regs mem md ly2 S2 U2 W2 regs2 regsc memc mdc k2 HJ HARU HRO Hspc R1 HPc Hcs Hgp Htp Hs0.
assert (HSTKf : 0 <= STK_fuzz_free /\ STK_fuzz_free + 64 <= STK_pj_write) by (vm_compute; split; discriminate).
assert (Hra : raZ regsc = PJW_FREE_RET)
  by (unfold raZ; rewrite R1; unfold w64, PJW_FREE_RET; rewrite unsigned_lit_small by lia; reflexivity).
split; [|exact Hra].
apply (fsw_fpreU_atFP B STK_pj_write (spZ regs) FS_PSTAT_FP ly S U2 W (unpoison U mem) md [] ly2 S2 W2 memc mdc k2
  regsc STK_fuzz_free (-64) [] HJ HARU HRO).
- lia.
- reflexivity.
- lia.
- lia.
- lia.
- rewrite R1. apply YK0s.ret_ok_even. unfold w64, PJW_FREE_RET. rewrite unsigned_lit_small by lia. reflexivity.
- rewrite Hra. unfold PJW_FREE_RET. lia.
- rewrite (fsw_pres regs2 regsc 3%bv HPc ltac:(unfold acallee_saved; pjw_f_bvz; lia)).
  rewrite (Hcs 3%bv); [exact Hgp | ..]; unfold acallee_saved; pjw_f_bvz; lia.
- rewrite (fsw_pres regs2 regsc 4%bv HPc ltac:(unfold acallee_saved; pjw_f_bvz; lia)).
  rewrite (Hcs 4%bv); [exact Htp | ..]; unfold acallee_saved; pjw_f_bvz; lia.
- apply achain_low. unfold s0Z in *.
  rewrite (fsw_pres regs2 regsc 8%bv HPc ltac:(unfold acallee_saved; pjw_f_bvz; lia)). lia.
Qed.

(* the run PJW_FREE_RET .. ret: `li a0, 0`, the three reloads, `addi sp, sp, 64`, `ret` (pjw_epi_success's twin) *)
Lemma pjw_f_epi :
  forall (W : world tfibsegs) ly S U regs mem md ly3 S3 U3 (W3 : world tfibsegs) regs3 mem3 md3 k3 buf len cap
    (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly3 S3 W3 (unpoison U3 mem3) md3 k3 ->
  ARU tfibsegs B ly3 S3 U3 W3 mem3 md3 ->
  st_ok tfibsegs (Ereg regs3 (pjw_extra regs buf len cap)) (fss_ret PJW_FREE_RET 64 pjw_f_cs)
    (restrict (w_H W3) (YK11.mkst regs3 (Z_to_bv 64 PJW_FREE_RET) mem3 (YK11.seg_rom tfibsegs))) ->
  spZ regs3 = spZ regs - 64 ->
  (forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 2 -> bv_unsigned q <> 8 ->
     bv_unsigned q <> 9 -> getr regs3 q = getr regs q) ->
  YK0s.ret_ok (getr regs 1) ->
  (forall regsF memF mdF, getr regsF 10 = w64 0 ->
     ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
       ly3 S3 W3 (unpoison U3 memF) mdF k3 ->
     ARU tfibsegs B ly3 S3 U3 W3 memF mdF ->
     same_below mem3 memF alloc_ceiling ->
     Q ly3 S3 W3 regsF memF mdF) ->
  SRr tfibsegs W3 (cfg_at tfibsegs PJW_FREE_RET regs3 mem3 md3)
    (fpostU tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP regs ly S U W mem md k3 U3 Q).
Proof.
intros W ly S U regs mem md ly3 S3 U3 W3 regs3 mem3 md3 k3 buf len cap Q HJ HARU HS Hsp3 Hcs Hra HQ.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HARj & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTKv : 4160 <= STK_pj_write) by (vm_compute; discriminate).
set (E := Ereg regs3 (pjw_extra regs buf len cap)) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64)
  by (subst E; rewrite (ew_Ereg_nat regs3 (pjw_extra regs buf len cap) 2 2%bv eq_refl); exact Hsp3).
unfold cfg_at. change (w64 PJW_FREE_RET) with (Z_to_bv 64 PJW_FREE_RET).
fsw_aj_runU fsw_wr_tbl_ok HS HJ HARU.
{ fsw_awr_ret Usp 64. }
assert (SB : same_below mem3 (ms_mem ms) alloc_ceiling).
{ unfold fss_ret in HF. cbn [ss_mem] in HF.
  apply (same_below_frame1 E _ mem3 (ms_mem ms) alloc_ceiling HF);
    [cbn [YP09.r_base YP09.r_wlo base_val fstk_ret]; rewrite Usp; lia | lia]. }
pose proof (fsw_reg_extra (w_H W3) regs3 (pjw_extra regs buf len cap) _ ms 1%bv 0 HS
  ltac:(vm_compute; reflexivity)) as R1F.
pose proof (fsw_reg_lit (w_H W3) E _ ms 10%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R10F.
apply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok W3 E _ ms _ STK_pj_write (spZ regs) FS_PSTAT_FP regs ly S U W mem md
  ly3 S3 U3 k3 Q HS).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- rewrite R1F. cbn [nth pjw_extra]. exact Hra.
- exact HJ.
- exact HARU.
- apply (fsw_preserved (w_H W3) E _ ms regs pjw_expect HS); [vm_compute; reflexivity|].
  intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (pjw_expect ?q) = _ =>
    let e := eval vm_compute in (pjw_expect q) in change (pjw_expect q) with e end;
  try first
  [ exact (fsw_sp_back regs3 (pjw_extra regs buf len cap) regs 64 Usp)
  | rewrite fsw_SOff0; subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity
  | rewrite fsw_SOff0; subst E; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity ].
  all: rewrite fsw_SOff0; subst E.
  all: lazymatch goal with |- ew _ ?n = getr _ ?q => rewrite (ew_Ereg_nat _ _ n q eq_refl) end.
  all: apply Hcs; try (unfold acallee_saved); pjw_f_bvz; lia.
- intros mat2.
  pose proof (ajournal_materialize tfibsegs _ LAWS fs_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat2 HJ) as HJm.
  apply HQ.
  + rewrite R10F. reflexivity.
  + exact HJm.
  + destruct HARU as (_ & OK & PO). split; [exact (proj1 HJm) | split; [exact OK | exact PO]].
  + exact SB.
Qed.

Lemma pjw_epi_failed_null :
  forall (W : world tfibsegs) ly S U regs mem md ly2 S2 U2 (W2 : world tfibsegs) regs2 mem2 md2 k2 buf len cap
    live peak cnt fail
    (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 mem2) md2 k2 ->
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 ->
  st_ok tfibsegs (Ereg regs2 (pjw_extra regs buf len cap)) (fss_ret PJW_PUT_RET 64 (pjw_cs_obj 1))
    (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 PJW_PUT_RET) mem2 (YK11.seg_rom tfibsegs))) ->
  spZ regs2 = spZ regs - 64 ->
  (forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 2 -> bv_unsigned q <> 8 ->
     bv_unsigned q <> 9 -> getr regs2 q = getr regs q) ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  0 <= s0Z regs2 < alloc_ceiling ->
  fuzz_free_spec tfibsegs B ->
  fs_glob tfibsegs W2 mem2 live peak cnt fail -> fs_heads B ly2 S2 U2 ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) mem2) ->
  buf = 0 ->
  (forall ly3 S3 W3 regsF memF mdF, getr regsF 10 = w64 0 ->
     ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
       ly3 S3 W3 (unpoison U2 memF) mdF (k2 + 0) ->
     ARU tfibsegs B ly3 S3 U2 W3 memF mdF ->
     ablocks B ly3 S3 = ablocks B ly2 S2 -> fs_heads B ly3 S3 U2 -> fs_glob tfibsegs W3 memF live peak cnt fail ->
     Q ly3 S3 W3 regsF memF mdF) ->
  SRr tfibsegs W2 (cfg_at tfibsegs PJW_PUT_RET regs2 mem2 md2)
    (fpostU tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP regs ly S U W mem md (k2 + 0) U2 Q).
Proof.
intros W ly S U regs mem md ly2 S2 U2 W2 regs2 mem2 md2 k2 buf len cap live peak cnt fail Q
  HJ HARU HS Hsp2 Hcs Hra Hgp Htp Hs0 HFF Hglob Hheads HRO Hb0 HQ.
assert (HSTKf : 0 <= STK_fuzz_free /\ STK_fuzz_free + 64 <= STK_pj_write) by (vm_compute; split; discriminate).
apply (pjw_f_to_call W ly S U regs mem md ly2 S2 U2 W2 regs2 mem2 md2 k2 buf len cap _ HJ HARU HS Hsp2).
intros regsc memc mdc HJc0 HARUc SB Hspc R1 R10 HPc CHK.
pose proof (pjw_avb_of_same_below W2 mem2 memc SB) as AV.
destruct (pjw_f_fpre W ly S U regs mem md ly2 S2 U2 W2 regs2 regsc memc mdc k2 HJc0 HARUc
  (pjw_arodata_avb W2 mem2 memc AV HRO) Hspc R1 HPc Hcs Hgp Htp Hs0) as [HPRE Hrac].
eapply SRr_bind.
{ exact (HFF ly2 S2 U2 W2 regsc memc mdc [] buf 0 live peak cnt fail
    R10 (pjw_fs_glob_avb W2 mem2 memc live peak cnt fail AV Hglob) Hheads
    (or_introl (conj Hb0 HPRE)) (fun Hp => False_ind _ (Hp Hb0))). }
cbv beta. intros W3 c3 _ [(_ & HPOST) | (Hpn & _)]; [|exfalso; exact (Hpn Hb0)].
unfold apost_baseU, fpostU in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJf & OK3 & PO3 & HP3 & Hab3 & Hheads3 & Hglob3).
rewrite R1.
destruct (fsw_after_callFPU B STK_pj_write (spZ regs) FS_PSTAT_FP [] ly S U W2 mem md W ly2 S2 U2 memc mdc k2
  STK_fuzz_free [] 64 regsc ly3 S3 U2 W3 regs3 mem3 md3 0 (pjw_extra regs buf len cap) pjw_f_cs PJW_FREE_RET
  HJc0 HARUc HJf ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) OK3 PO3 HP3 Hspc ltac:(lia) (proj1 HSTKf)
  ltac:(lia) ltac:(reflexivity) ltac:(vm_compute; reflexivity) pjw_f_cs_in (CHK regs3)) as (HJ3 & HARU3 & HS3).
apply (pjw_f_epi W ly S U regs mem md ly3 S3 U2 W3 regs3 mem3 md3 (k2 + 0) buf len cap Q HJ3 HARU3 HS3).
- unfold spZ at 1. rewrite (fsw_pres regsc regs3 2%bv HP3 ltac:(unfold acallee_saved; pjw_f_bvz; lia)). exact Hspc.
- intros q Hq H2 H8 H9. rewrite (fsw_pres regsc regs3 q HP3 Hq), (fsw_pres regs2 regsc q HPc Hq).
  exact (Hcs q Hq H2 H8 H9).
- exact Hra.
- intros regsF memF mdF H10 HJF HARUF SBF.
  apply HQ; [exact H10 | exact HJF | exact HARUF | exact Hab3 | exact Hheads3 |].
  exact (pjw_fs_glob_avb W3 mem3 memF live peak cnt fail (pjw_avb_of_same_below W3 mem3 memF SBF) Hglob3).
Qed.

Lemma pjw_epi_failed_block :
  forall (W : world tfibsegs) ly S U regs mem md ly2 S2 U2 (W2 : world tfibsegs) regs2 mem2 md2 k2 buf len cap
    live peak cnt fail n U1 U2'
    (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 mem2) md2 k2 ->
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 ->
  st_ok tfibsegs (Ereg regs2 (pjw_extra regs buf len cap)) (fss_ret PJW_PUT_RET 64 (pjw_cs_obj 1))
    (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 PJW_PUT_RET) mem2 (YK11.seg_rom tfibsegs))) ->
  spZ regs2 = spZ regs - 64 ->
  (forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 2 -> bv_unsigned q <> 8 ->
     bv_unsigned q <> 9 -> getr regs2 q = getr regs q) ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  0 <= s0Z regs2 < alloc_ceiling ->
  fuzz_free_spec tfibsegs B ->
  fs_glob tfibsegs W2 mem2 live peak cnt fail -> fs_heads B ly2 S2 U2 -> st_nev S2 + 1 <= EV_MAX ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) mem2) ->
  buf <> 0 -> U2 = U1 ++ (buf - HEAD, HEAD) :: U2' -> fs_rblock tfibsegs B ly2 S2 W2 mem2 buf n -> n <= live ->
  ~ In (buf - HEAD, n + HEAD) (ablocks B ly S) ->
  (forall ly3 S3 W3 regsF memF mdF, getr regsF 10 = w64 0 ->
     ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
       ly3 S3 W3 (unpoison (U1 ++ U2') memF) mdF (k2 + 1) ->
     ARU tfibsegs B ly3 S3 (U1 ++ U2') W3 memF mdF ->
     (exists l1 l2, ablocks B ly2 S2 = l1 ++ (buf - HEAD, n + HEAD) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
     fs_heads B ly3 S3 (U1 ++ U2') -> fs_glob tfibsegs W3 memF (live - n) peak cnt fail ->
     Q ly3 S3 W3 regsF memF mdF) ->
  SRr tfibsegs W2 (cfg_at tfibsegs PJW_PUT_RET regs2 mem2 md2)
    (fpostU tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP regs ly S U W mem md (k2 + 1) (U1 ++ U2') Q).
Proof.
intros W ly S U regs mem md ly2 S2 U2 W2 regs2 mem2 md2 k2 buf len cap live peak cnt fail n U1 U2' Q
  HJ HARU HS Hsp2 Hcs Hra Hgp Htp Hs0 HFF Hglob Hheads Hev HRO Hb0 EU2 Hrb Hnl Hnotin HQ.
assert (HSTKf : 0 <= STK_fuzz_free /\ STK_fuzz_free + 64 <= STK_pj_write) by (vm_compute; split; discriminate).
apply (pjw_f_to_call W ly S U regs mem md ly2 S2 U2 W2 regs2 mem2 md2 k2 buf len cap _ HJ HARU HS Hsp2).
intros regsc memc mdc HJc0 HARUc SB Hspc R1 R10 HPc CHK.
pose proof (pjw_avb_of_same_below W2 mem2 memc SB) as AV.
destruct (pjw_f_fpre W ly S U regs mem md ly2 S2 U2 W2 regs2 regsc memc mdc k2 HJc0 HARUc
  (pjw_arodata_avb W2 mem2 memc AV HRO) Hspc R1 HPc Hcs Hgp Htp Hs0) as [HPRE Hrac].
assert (Hrbc : fs_rblock tfibsegs B ly2 S2 W2 memc buf n)
  by exact (pjw_rblock_avb ly2 S2 W2 mem2 memc _ _ buf n (proj1 HARU) AV Hrb).
(* the freed block's footprint: the statics are image bytes, the block was taken inside pj_write *)
assert (HFPS : fsw_fp_sub B ly S ly2 S2 [] FS_PSTAT_FP (FS_PSTAT_FP ++ ablocks_fp [(buf - HEAD, n + HEAD)])).
{ intros a Ha. apply inFP_app in Ha as [Ha|Ha].
  - right; right; left. split; [exact Ha | exact (pjw_f_pstat_img a Ha)].
  - right; left. destruct Ha as (r & Hr & Hra'). cbn [ablocks_fp map In] in Hr.
    destruct Hr as [<-|[]]. cbn [fst snd] in Hra'.
    exists (buf - HEAD), (n + HEAD). split; [exact (proj1 Hrb) | split; [exact Hnotin | lia]]. }
eapply SRr_bind.
{ exact (HFF ly2 S2 U2 W2 regsc memc mdc [] buf n live peak cnt fail
    R10 (pjw_fs_glob_avb W2 mem2 memc live peak cnt fail AV Hglob) Hheads
    (or_intror (conj Hb0 (ex_intro _ U1 (ex_intro _ U2' (conj EU2 (conj HPRE (conj Hrbc Hnl)))))))
    (fun _ => Hev)). }
cbv beta. intros W3 c3 _ [(Hp0 & _) | (_ & V1 & V2 & EV & HPOST)]; [exfalso; exact (Hb0 Hp0)|].
destruct (pjw_f_split_uniq (buf - HEAD, HEAD) U1 U2' V1 V2
  ltac:(rewrite <- EU2; exact (proj2 (proj1 (proj2 HARUc))))
  ltac:(unfold zdisjoint; cbn [fst snd]; unfold HEAD; lia)
  ltac:(rewrite <- EU2; exact EV)) as [<- <-].
unfold apost_baseU, fpostU in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJf & OK3 & PO3 & HP3 & Hab3 & Hheads3 & Hglob3).
rewrite R1.
destruct (fsw_after_callFPU B STK_pj_write (spZ regs) FS_PSTAT_FP [] ly S U W2 mem md W ly2 S2 U2 memc mdc k2
  STK_fuzz_free (FS_PSTAT_FP ++ ablocks_fp [(buf - HEAD, n + HEAD)]) 64 regsc ly3 S3 (U1 ++ U2') W3 regs3 mem3 md3 1
  (pjw_extra regs buf len cap) pjw_f_cs PJW_FREE_RET
  HJc0 HARUc HJf HFPS OK3 PO3 HP3 Hspc ltac:(lia) (proj1 HSTKf) ltac:(lia) ltac:(reflexivity)
  ltac:(vm_compute; reflexivity) pjw_f_cs_in (CHK regs3)) as (HJ3 & HARU3 & HS3).
apply (pjw_f_epi W ly S U regs mem md ly3 S3 (U1 ++ U2') W3 regs3 mem3 md3 (k2 + 1) buf len cap Q HJ3 HARU3 HS3).
- unfold spZ at 1. rewrite (fsw_pres regsc regs3 2%bv HP3 ltac:(unfold acallee_saved; pjw_f_bvz; lia)). exact Hspc.
- intros q Hq H2 H8 H9. rewrite (fsw_pres regsc regs3 q HP3 Hq), (fsw_pres regs2 regsc q HPc Hq).
  exact (Hcs q Hq H2 H8 H9).
- exact Hra.
- intros regsF memF mdF H10 HJF HARUF SBF.
  apply HQ; [exact H10 | exact HJF | exact HARUF | exact Hab3 | exact Hheads3 |].
  exact (pjw_fs_glob_avb W3 mem3 memF (live - n) peak cnt fail (pjw_avb_of_same_below W3 mem3 memF SBF) Hglob3).
Qed.


(* a stack byte is never a user-poisoned shadow byte: every range of U sits below kHighMemBeg *)
Lemma pjw_p_stack_not_ush : forall ly S U (W : world tfibsegs) m md a, ARU tfibsegs B ly S U W m md ->
  alloc_ceiling <= a < 2 ^ 64 -> in_ush U (bv_unsigned (Z_to_bv 64 a)) = false.
Proof.
intros ly S U W m md a HARU Ha.
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E; [|reflexivity]. exfalso.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite (wz a ltac:(lia)) in E.
destruct (ush_facts tfibsegs B ly S U W m md a HARU E) as (_ & _ & L2). lia.
Qed.

(* helpers of the folded put call, from the same scratch tree *)
Definition pjw_st_nl (failed : Z) (text : list Z) (cnt fail cap : Z) : WriterApp.wst :=
  WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [10].

(* a byte run below alloc_ceiling rides across on pjw_avb *)
Lemma pjw_p_zbytes_avb : forall (W : world tfibsegs) m m' p l, pjw_avb W m m' ->
  0 <= p -> p + Z.of_nat (length l) <= alloc_ceiling ->
  zbytes_at tfibsegs W m p l -> zbytes_at tfibsegs W m' p l.
Proof.
intros W m m' p l Hv Hp Hl H j Hj. destruct (H j Hj) as (Hval & Hb). split; [|exact Hb].
apply (pjw_t_val_mem W m m' (p + Z.of_nat j) 1 (nth j l 0) Hv); [lia | cbn [Z.of_nat]; lia | exact Hval].
Qed.


(* hence a stack byte whose unpoisoned view the journal keeps is kept on the machine's own memories *)
Lemma pjw_p_above_kept : forall ly S U (W : world tfibsegs) m md ly' S' U' (W' : world tfibsegs) m' md' a,
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  alloc_ceiling <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W') (unpoison U' m') a = aview tfibsegs (w_H W) (unpoison U m) a ->
  mrestrict (w_H W') m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a).
Proof.
intros ly S U W m md ly' S' U' W' m' md' a HARU HARU' Ha E.
pose proof fs_segs_low as HSL. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite (aview_unpoison_out tfibsegs _ U' m' a (pjw_p_stack_not_ush ly' S' U' W' m' md' a HARU' Ha)) in E.
rewrite (aview_unpoison_out tfibsegs _ U m a (pjw_p_stack_not_ush ly S U W m md a HARU Ha)) in E.
assert (Hni : ~ in_img tfibsegs a) by (intros Hi; pose proof (HSL a Hi) as HL; unfold kLowMemEnd in *; lia).
pose proof (mbyte_of_aview tfibsegs _ _ _ _ a E) as Em.
unfold mbyte in Em. rewrite (seg_rom_none tfibsegs a ltac:(lia) Hni) in Em.
destruct (mrestrict (w_H W') m' (Z_to_bv 64 a)), (mrestrict (w_H W) m (Z_to_bv 64 a)); congruence.
Qed.

(* The pretty <> 0 put call, proved by a part agent of a Theorem Labs lane in its scratch tree over this file and folded
   here by the lane parent: the call of put for the final newline and its resume. *)

Lemma pjw_put_call : forall (W : world tfibsegs) ly S U regs mem md ly2 S2 U2 (W2 : world tfibsegs)
  regs2 mem2 md2 k2 pretty buf cap failed (text : list Z) live peak cnt fail
  (Q : world tfibsegs -> config -> Prop),
  put_spec B tfibsegs ->
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 mem2) md2 k2 ->
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 ->
  st_ok tfibsegs (Ereg regs2 (pjw_extra regs buf (Z.of_nat (length text)) cap))
    (fss_ret PJW_WV_RET 64 (pjw_cs_obj failed))
    (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 PJW_WV_RET) mem2 (YK11.seg_rom tfibsegs))) ->
  spZ regs2 = spZ regs - FRAME_pj_write ->
  getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
  getr regs2 8 = w64 pretty -> pretty <> 0 -> 0 <= pretty < alloc_ceiling ->
  wout_ok B tfibsegs ly2 S2 W2 mem2 (spZ regs - 56) buf cap failed text ->
  fs_glob tfibsegs W2 mem2 live peak cnt fail ->
  (cap <> 0 -> In (buf - HEAD, HEAD) U2) ->
  fs_heads B ly2 S2 U2 ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) mem2) ->
  fs_img_facts tfibsegs B ->
  fsw_fp_sub B ly S ly2 S2 [] FS_PSTAT_FP (FS_PSTAT_FP ++ wbuf_fp buf cap) ->
  Z.of_nat (length (frames S2)) <= FRL_CRT_CALLEE + 1 ->
  cap <= WMAX -> cap <= live -> Z.of_nat (length text) + 1 + 1 <= WMAX ->
  wbudget_pre S2 cap cnt live (pjw_st_nl failed text cnt fail cap) ->
  (forall ly3 S3 (W3 : world tfibsegs) U3 regsE memE mdE buf',
     ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
       ly3 S3 W3 (unpoison U3 memE) mdE (k2 + wevk cap (pjw_st_nl failed text cnt fail cap)) ->
     ARU tfibsegs B ly3 S3 U3 W3 memE mdE ->
     st_ok tfibsegs (Ereg regsE (pjw_extra regs buf'
         (Z.of_nat (length (WriterApp.w_text (pjw_st_nl failed text cnt fail cap))))
         (WriterApp.w_cap (pjw_st_nl failed text cnt fail cap))))
       (fss_ret PJW_PUT_RET 64 (pjw_cs_obj (WriterApp.w_failed (pjw_st_nl failed text cnt fail cap))))
       (restrict (w_H W3) (YK11.mkst regsE (Z_to_bv 64 PJW_PUT_RET) memE (YK11.seg_rom tfibsegs))) ->
     spZ regsE = spZ regs - FRAME_pj_write ->
     (forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regsE q = getr regs2 q) ->
     uswap U2 U3 buf buf' cap ->
     wout_ok B tfibsegs ly3 S3 W3 memE (spZ regs - 56) buf'
       (WriterApp.w_cap (pjw_st_nl failed text cnt fail cap))
       (WriterApp.w_failed (pjw_st_nl failed text cnt fail cap))
       (WriterApp.w_text (pjw_st_nl failed text cnt fail cap)) ->
     wbudget_kept S2 S3 failed cap cnt (WriterApp.w_failed (pjw_st_nl failed text cnt fail cap))
       (WriterApp.w_cap (pjw_st_nl failed text cnt fail cap))
       (WriterApp.w_cnt (pjw_st_nl failed text cnt fail cap)) ->
     bswap (ablocks B ly2 S2) (ablocks B ly3 S3) buf buf' cap
       (WriterApp.w_cap (pjw_st_nl failed text cnt fail cap)) ->
     (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap (pjw_st_nl failed text cnt fail cap)) /\
        fs_glob tfibsegs W3 memE (live + WriterApp.w_cap (pjw_st_nl failed text cnt fail cap) - cap) peak'
          (WriterApp.w_cnt (pjw_st_nl failed text cnt fail cap))
          (WriterApp.w_fail (pjw_st_nl failed text cnt fail cap))) ->
     SRr tfibsegs W3 (cfg_at tfibsegs PJW_PUT_RET regsE memE mdE) Q) ->
  SRr tfibsegs W2 (cfg_at tfibsegs PJW_WV_RET regs2 mem2 md2) Q.
Proof.
intros W ly S U regs mem md ly2 S2 U2 W2 regs2 mem2 md2 k2 pretty buf cap failed text live peak cnt fail Q
  HPUT HJ HARU HS Hsp2 Hgp Htp H8 Hpnz Hpr HOUT HGLOB HUin HHEADS HRO HIMG HFPSUB HFRL HcapM Hlive HlenM HBUD K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HOUT as (Ho8 & Ho0 & Hotop & Hoacc & Hbufr & Hcapr & Vb2 & Vl2 & Vc2 & Vf2 & Hf01 & Hbok & Hdisj).
assert (Hlenr : 0 <= Z.of_nat (length text) < 2 ^ 64).
{ destruct Hdisj as [(_ & _ & Ht0)|(_ & _ & Hlt & _)]; [rewrite Ht0; cbn [length Z.of_nat]; lia | lia]. }
unfold FRAME_pj_write in Hsp2.
assert (HSTKv : 4160 <= STK_pj_write) by (vm_compute; discriminate).
assert (HSTKp : STK_put + 64 <= STK_pj_write) by (vm_compute; discriminate).
assert (HSTKp0 : 0 <= STK_put) by (vm_compute; discriminate).
set (E := Ereg regs2 (pjw_extra regs buf (Z.of_nat (length text)) cap)) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64)
  by (subst E; rewrite (ew_Ereg_nat regs2 (pjw_extra regs buf (Z.of_nat (length text)) cap) 2 2%bv eq_refl);
      exact Hsp2).
assert (E8 : ew E 8 = Z_to_bv 64 pretty)
  by (subst E; rewrite (ew_Ereg_nat regs2 (pjw_extra regs buf (Z.of_nat (length text)) cap) 8 8%bv eq_refl);
      exact H8).
unfold cfg_at. change (w64 PJW_WV_RET) with (Z_to_bv 64 PJW_WV_RET).
srr_branch_with fsw_wr_tbl_ok HS.
- (* taken: that is pretty = 0, which this arm excludes *)
  exfalso. rewrite branch_eq_U in Hc.
  rewrite (U_atom E 8 pretty E8 ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hc.
  apply Z.eqb_eq in Hc. lia.
- (* not taken: the five instructions of the call, then put *)
  fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU A_put.
  { fsw_awr_ret Usp 64. }
  assert (SB : same_below mem2 (ms_mem ms) alloc_ceiling).
  { unfold fss_ret in HF. cbn [add_cond ss_mem] in HF.
    apply (same_below_frame1 E _ mem2 (ms_mem ms) alloc_ceiling HF);
      [cbn [YP09.r_base YP09.r_wlo base_val fstk_ret]; rewrite Usp; lia | lia]. }
  pose proof (pjw_avb_of_same_below W2 mem2 (ms_mem ms) SB) as AVB.
  pose proof HJ as (HARj & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _ & _).
  (* the registers the five instructions set *)
  pose proof (fsw_reg_lit (w_H W2) E _ ms 1%bv PJW_PUT_RET HS ltac:(vm_compute; reflexivity)
    ltac:(unfold PJW_PUT_RET; lia)) as R1.
  pose proof (fsw_reg_off (w_H W2) E _ ms 2%bv 2 0 (spZ regs - 64) HS ltac:(vm_compute; reflexivity) Usp
    ltac:(lia)) as R2.
  assert (R2z : spZ (ms_regs ms) = spZ regs - 64 + 0) by exact R2.
  assert (R2' : spZ (ms_regs ms) = spZ regs - 64) by lia.
  pose proof (fsw_reg_atom (w_H W2) regs2 (pjw_extra regs buf (Z.of_nat (length text)) cap) _ ms 3%bv 3%bv 3 HS
    ltac:(vm_compute; reflexivity) eq_refl) as R3.
  pose proof (fsw_reg_atom (w_H W2) regs2 (pjw_extra regs buf (Z.of_nat (length text)) cap) _ ms 4%bv 4%bv 4 HS
    ltac:(vm_compute; reflexivity) eq_refl) as R4.
  pose proof (fsw_reg_atom (w_H W2) regs2 (pjw_extra regs buf (Z.of_nat (length text)) cap) _ ms 8%bv 8%bv 8 HS
    ltac:(vm_compute; reflexivity) eq_refl) as R8.
  pose proof (fsw_reg_off (w_H W2) E _ ms 10%bv 2 8 (spZ regs - 64) HS ltac:(vm_compute; reflexivity) Usp
    ltac:(lia)) as R10.
  pose proof (fsw_reg_lit (w_H W2) E _ ms 11%bv PJW_STR_NL HS ltac:(vm_compute; reflexivity)
    ltac:(unfold PJW_STR_NL; lia)) as R11.
  pose proof (fsw_reg_lit (w_H W2) E _ ms 12%bv 1 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R12.
  assert (Hra : raZ (ms_regs ms) = PJW_PUT_RET)
    by (unfold raZ; rewrite R1; rewrite unsigned_lit_small by (unfold PJW_PUT_RET; lia); reflexivity).
  assert (Hs0 : s0Z (ms_regs ms) = pretty)
    by (unfold s0Z; rewrite R8, H8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  (* the object's four fields and the three saved words, read off the state's own chunks *)
  pose proof (fsw_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 8 8%N (SOff 35 0) buf HR0 Usp ltac:(cbn; tauto)
    ltac:(rewrite fsw_SOff0; subst E; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra;
          cbn [nth pjw_extra]; reflexivity)
    ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V8.
  pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 16 8%N (SOff 36 0) (Z.of_nat (length text)) HR0 Usp
    ltac:(cbn; tauto)
    ltac:(rewrite fsw_SOff0; subst E; change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra;
          cbn [nth pjw_extra]; reflexivity)
    ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V16.
  pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 24 8%N (SOff 37 0) cap HR0 Usp ltac:(cbn; tauto)
    ltac:(rewrite fsw_SOff0; subst E; change 37%nat with (32 + 5)%nat; rewrite ew_Ereg_extra;
          cbn [nth pjw_extra]; reflexivity)
    ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V24.
  pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 32 4%N (SLit failed) failed HR0 Usp ltac:(cbn; tauto)
    ltac:(reflexivity) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V32.
  pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 40 8%N (SOff 34 0) (bv_unsigned (getr regs 9)) HR0 Usp
    ltac:(cbn; tauto)
    ltac:(rewrite fsw_SOff0; subst E; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra;
          cbn [nth pjw_extra]; symmetry; apply Z_to_bv_bv_unsigned)
    ltac:(cbn [Z.of_N]; apply u64_range) ltac:(cbn [Z.of_N]; lia)) as V40.
  pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 48 8%N (SOff 33 0) (s0Z regs) HR0 Usp ltac:(cbn; tauto)
    ltac:(rewrite fsw_SOff0; subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra;
          cbn [nth pjw_extra]; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned)
    ltac:(cbn [Z.of_N]; unfold s0Z; apply u64_range) ltac:(cbn [Z.of_N]; lia)) as V48.
  pose proof (fsw_field E _ 2 (spZ regs - 64) _ _ _ _ _ 56 8%N (SOff 32 0) (raZ regs) HR0 Usp ltac:(cbn; tauto)
    ltac:(rewrite fsw_SOff0; subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra;
          cbn [nth pjw_extra]; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned)
    ltac:(cbn [Z.of_N]; unfold raZ; apply u64_range) ltac:(cbn [Z.of_N]; lia)) as V56.
  clear HR0.
  pose proof (aregs_preserved_of_st_ok tfibsegs (w_H W2) E _ ms regs2
    (pjw_extra regs buf (Z.of_nat (length text)) cap) HS ltac:(apply env_agree_refl)
    ltac:(vm_compute; reflexivity)) as HPRS0.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) E _ ms HS ltac:(vm_compute; reflexivity)). cbn [ss_pc].
  (* ---- put's premises at the call ---- *)
  eapply SRr_bind.
  { eapply (HPUT ly2 S2 U2 W2 (ms_regs ms) (ms_mem ms) _ [] (spZ regs - 16) (spZ regs - 56) PJW_STR_NL 1
      buf cap failed text [10] live peak cnt fail).
    - (* fpreU at the call *)
      eapply (fsw_fpreU_atFP B STK_pj_write (spZ regs) FS_PSTAT_FP ly S U2 W (unpoison U mem) md [] ly2 S2 W2
        (ms_mem ms) _ k2 (ms_regs ms) STK_put (-64) []).
      + exact HJ.
      + exact HARU.
      + exact (pjw_arodata_avb W2 mem2 (ms_mem ms) AVB HRO).
      + lia.
      + reflexivity.
      + lia.
      + exact HSTKp0.
      + lia.
      + rewrite R1. apply YK0s.ret_ok_even.
        rewrite unsigned_lit_small by (unfold PJW_PUT_RET; lia). reflexivity.
      + rewrite Hra. unfold PJW_PUT_RET. lia.
      + rewrite R3. exact Hgp.
      + rewrite R4. exact Htp.
      + apply achain_low. rewrite Hs0. lia.
    - exact HHEADS.
    - exact HFRL.
    - apply bv_eq. etransitivity; [exact R10|]. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - exact R11.
    - exact R12.
    - (* the object on the call memory *)
      unfold wout_ok.
      split; [lia|]. split; [lia|]. split; [rewrite Etop; lia|].
      split.
      { intros i Hi.
        assert (Hp : apresent (w_H W2) (ms_mem ms) (spZ regs - 56 + i)).
        { apply (fsw_apresent_unpoison B ly2 S2 U2 W2 (ms_mem ms) _ (spZ regs - 56 + i) HARU); [lia|].
          apply Hpres. lia. }
        split; [exact (apresent_writable tfibsegs _ _ _ Hp) | exact Hp]. }
      split; [exact Hbufr|]. split; [exact Hcapr|].
      split; [replace (spZ regs - 56) with (spZ regs - 64 + 8) by lia; exact V8|].
      split; [replace (spZ regs - 56 + 8) with (spZ regs - 64 + 16) by lia; exact V16|].
      split; [replace (spZ regs - 56 + 16) with (spZ regs - 64 + 24) by lia; exact V24|].
      split; [replace (spZ regs - 56 + 24) with (spZ regs - 64 + 32) by lia; exact V32|].
      split; [exact Hf01|]. split; [exact Hbok|].
      destruct Hdisj as [(Hc0 & Hb0 & Ht0)|(Hcj & Hrb & Hlt & Hz)].
      + left. split; [exact Hc0|]. split; [exact Hb0 | exact Ht0].
      + right. split; [exact Hcj|].
        pose proof Hrb as (Hbin & _ & _ & _).
        destruct (fsw_ablock_low B ly2 S2 W2 _ _ _ _ HARj Hbin) as (A1 & A2 & A3).
        split; [exact (pjw_rblock_avb ly2 S2 W2 mem2 (ms_mem ms) _ _ buf cap HARj AVB Hrb)|].
        split; [exact Hlt|].
        apply (pjw_p_zbytes_avb W2 mem2 (ms_mem ms) buf (text ++ [0]) AVB);
          [unfold HEAD in *; lia | rewrite length_app; cbn [length]; unfold HEAD, req_size in *; lia | exact Hz].
    - exact (pjw_fs_glob_avb W2 mem2 (ms_mem ms) live peak cnt fail AVB HGLOB).
    - exact HUin.
    - lia.
    - lia.
    - replace ((spZ regs - 16) mod 16) with (spZ regs mod 16); [exact Hal16|].
      rewrite <- (Z.mod_add (spZ regs - 16) 1 16) by lia. f_equal. lia.
    - rewrite Etop. lia.
    - left. split; [lia|]. rewrite Hra. unfold PJW_PUT_RET. lia.
    - intros a Ha. apply (fsw_apresent_unpoison B ly2 S2 U2 W2 (ms_mem ms) _ a HARU); [lia|].
      apply Hpres. lia.
    - apply (pjw_ro_lit_kept ly2 S2 U2 W2 (ms_mem ms) _ HARU).
      + apply (proj1 (pjw_j_arodata_unpoison ly2 S2 U2 W2 (ms_mem ms) _ HARU)).
        exact (pjw_arodata_avb W2 mem2 (ms_mem ms) AVB HRO).
      + exact HIMG.
      + vm_compute. tauto.
    - right. right. right. exists [10]. split; [vm_compute; tauto|].
      cbn [length]. apply le_S. apply le_n.
    - reflexivity.
    - repeat constructor. lia.
    - unfold PJW_STR_NL. lia.
    - left. unfold PJW_STR_NL. lia.
    - exact HlenM.
    - exact HcapM.
    - exact Hlive.
    - exact HBUD. }
  (* ---- put's post, composed back into the caller's journal ---- *)
  cbv beta. intros W3 c3 Hwle (st' & buf' & U3 & Est & Husw & Hpost).
  unfold wpost, fpostU in Hpost.
  destruct Hpost as (ly3 & S3 & regs3 & mem3 & md3 & Ec3 & HJc & OK3 & PO3 & HPRS & HOUT3 & HKEPT & HBSW & HWK &
    HGL3 & HSRC3).
  subst c3. subst st'.
  assert (HARU3 : ARU tfibsegs B ly3 S3 U3 W3 mem3 md3)
    by (split; [exact (proj1 HJc) | split; [exact OK3 | exact PO3]]).
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & Habove & _).
  pose proof HOUT3 as (_ & _ & _ & _ & Hbufr3 & Hcapr3 & Vb3 & Vl3 & Vc3 & Vf3 & Hf013 & _ & Hdisj3).
  assert (Hlenr3 : 0 <= Z.of_nat (length (WriterApp.w_text
                     (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [10]))) < 2 ^ 64).
  { destruct Hdisj3 as [(_ & _ & Ht0)|(_ & _ & Hlt & _)]; [rewrite Ht0; cbn [length Z.of_nat]; lia | lia]. }
  (* the three saved words on the memory after the call *)
  assert (V40' : val_mem tfibsegs (mrestrict (w_H W3) mem3) (spZ regs - 24) 8 (bv_unsigned (getr regs 9))).
  { intros k Hk. rewrite (proj1 (HWK (spZ regs - 24 + Z.of_nat k) ltac:(lia) ltac:(lia))).
    replace (spZ regs - 24 + Z.of_nat k) with (spZ regs - 64 + 40 + Z.of_nat k) by lia. exact (V40 k Hk). }
  assert (KEEPUP : forall a, spZ regs - 16 <= a < spZ regs ->
    mrestrict (w_H W3) mem3 (Z_to_bv 64 a) = mrestrict (w_H W2) (ms_mem ms) (Z_to_bv 64 a)).
  { intros a Ha. apply (pjw_p_above_kept ly2 S2 U2 W2 (ms_mem ms) _ ly3 S3 U3 W3 mem3 md3 a HARU HARU3
      ltac:(lia)). apply Habove; lia. }
  assert (V48' : val_mem tfibsegs (mrestrict (w_H W3) mem3) (spZ regs - 16) 8 (s0Z regs)).
  { intros k Hk. pose proof (V48 k Hk) as Hv. unfold mbyte in *.
    rewrite (KEEPUP (spZ regs - 16 + Z.of_nat k) ltac:(lia)).
    replace (spZ regs - 16 + Z.of_nat k) with (spZ regs - 64 + 48 + Z.of_nat k) by lia. exact Hv. }
  assert (V56' : val_mem tfibsegs (mrestrict (w_H W3) mem3) (spZ regs - 8) 8 (raZ regs)).
  { intros k Hk. pose proof (V56 k Hk) as Hv. unfold mbyte in *.
    rewrite (KEEPUP (spZ regs - 8 + Z.of_nat k) ltac:(lia)).
    replace (spZ regs - 8 + Z.of_nat k) with (spZ regs - 64 + 56 + Z.of_nat k) by lia. exact Hv. }
  assert (CHK : Forall (YP09.chunk_ok tfibsegs (Ereg regs3 (pjw_extra regs buf'
      (Z.of_nat (length (WriterApp.w_text (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [10]))))
      (WriterApp.w_cap (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [10]))))
      (mrestrict (w_H W3) mem3) (spZ regs - 64))
      (pjw_cs_obj (WriterApp.w_failed (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [10])))).
  { unfold pjw_cs_obj. repeat constructor.
    - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 8 8%N (SOff 35 0) buf').
      + rewrite fsw_SOff0. change 35%nat with (32 + 3)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
        reflexivity.
      + cbn [Z.of_N]; lia.
      + cbn [Z.of_N]; lia.
      + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
        replace (spZ regs - 64 + 8) with (spZ regs - 56) by lia. exact Vb3.
    - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 16 8%N (SOff 36 0)
        (Z.of_nat (length (WriterApp.w_text (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [10]))))).
      + rewrite fsw_SOff0. change 36%nat with (32 + 4)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
        reflexivity.
      + cbn [Z.of_N]; lia.
      + cbn [Z.of_N]; lia.
      + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
        replace (spZ regs - 64 + 16) with (spZ regs - 56 + 8) by lia. exact Vl3.
    - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 24 8%N (SOff 37 0)
        (WriterApp.w_cap (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [10]))).
      + rewrite fsw_SOff0. change 37%nat with (32 + 5)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
        reflexivity.
      + cbn [Z.of_N]; lia.
      + cbn [Z.of_N]; lia.
      + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
        replace (spZ regs - 64 + 24) with (spZ regs - 56 + 16) by lia. exact Vc3.
    - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 32 4%N
        (SLit (WriterApp.w_failed (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [10])))
        (WriterApp.w_failed (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [10]))).
      + reflexivity.
      + cbn [Z.of_N]; lia.
      + cbn [Z.of_N]; lia.
      + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
        replace (spZ regs - 64 + 32) with (spZ regs - 56 + 24) by lia. exact Vf3.
    - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 40 8%N (SOff 34 0) (bv_unsigned (getr regs 9))).
      + rewrite fsw_SOff0. change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
        symmetry. apply Z_to_bv_bv_unsigned.
      + cbn [Z.of_N]. apply u64_range.
      + cbn [Z.of_N]; lia.
      + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
        replace (spZ regs - 64 + 40) with (spZ regs - 24) by lia. exact V40'.
    - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 48 8%N (SOff 33 0) (s0Z regs)).
      + rewrite fsw_SOff0. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
        unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned.
      + cbn [Z.of_N]. unfold s0Z. apply u64_range.
      + cbn [Z.of_N]; lia.
      + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
        replace (spZ regs - 64 + 48) with (spZ regs - 16) by lia. exact V48'.
    - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 56 8%N (SOff 32 0) (raZ regs)).
      + rewrite fsw_SOff0. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
        unfold raZ. symmetry. apply Z_to_bv_bv_unsigned.
      + cbn [Z.of_N]. unfold raZ. apply u64_range.
      + cbn [Z.of_N]; lia.
      + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
        replace (spZ regs - 64 + 56) with (spZ regs - 8) by lia. exact V56'. }
  destruct (fsw_after_callFPU_ot B STK_pj_write (spZ regs) FS_PSTAT_FP [] ly S U W2 mem md W ly2 S2 U2
    (ms_mem ms) _ k2 STK_put (FS_PSTAT_FP ++ wbuf_fp buf cap) (spZ regs - 16) 64 (ms_regs ms)
    ly3 S3 U3 W3 regs3 mem3 md3
    (wevk cap (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [10]))
    (pjw_extra regs buf'
      (Z.of_nat (length (WriterApp.w_text (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [10]))))
      (WriterApp.w_cap (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [10])))
    (pjw_cs_obj (WriterApp.w_failed (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [10])))
    PJW_PUT_RET
    HJ HARU HJc HFPSUB OK3 PO3 HPRS ltac:(lia) ltac:(lia) HSTKp0 ltac:(lia) ltac:(reflexivity)
    ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) CHK)
    as (HJ4 & HARU4 & HS4).
  pose proof (aregs_preserved_trans regs2 (ms_regs ms) regs3 HPRS0 HPRS) as HPRSall.
  assert (HCS : forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regs3 q = getr regs2 q).
  { intros q Hq. pose proof (HPRSall (bv_unsigned q) Hq) as Eq. rewrite Z_to_bv_bv_unsigned in Eq. exact Eq. }
  rewrite R1.
  apply (K ly3 S3 W3 U3 regs3 mem3 md3 buf').
  + exact HJ4.
  + exact HARU4.
  + exact HS4.
  + unfold spZ, FRAME_pj_write. rewrite (HCS 2%bv ltac:(unfold acallee_saved; left; reflexivity)).
    exact Hsp2.
  + exact HCS.
  + exact Husw.
  + exact HOUT3.
  + exact HKEPT.
  + exact HBSW.
  + exact HGL3.
Qed.

(* stage 5, proved by a part agent of a Theorem Labs lane in its scratch tree over b6c5b22a453, pasted unchanged *)
(* ================= stage 5: the call of write_value at level 0 and its return =================
   The walk is at the callee's entry (pjw_to_write_value leaves it there). This is write_value's spec at level 0
   with its premises from pjw_wv_premises (stage 4), and its post composed back into pj_write's journal with
   FSW_K3.fsw_after_callFPU_ot, rebuilding the seven chunks of pjw_cs_obj on the memory AFTER the call: the
   object's four fields from wout_ok, the saved s1 word at sp - 24 from the callee's wkeep, and the saved s0 / ra
   words at sp - 16 / sp - 8 from the callee journal's above-the-window clause through pjw_p_above_kept. The
   shape is pjw_put_call's, at the first call of the walk instead of the last. *)
(* the writer state after write_value at level 0 from the zeroed pj_out *)
Definition pjw_st_wv (t : PjTree.jv) (p : bool) (cnt fail : Z) : WriterApp.wst :=
  WriterApp.putN (WriterApp.mkW 0 [] 0 cnt fail []) (WriterValue.wvpieces t p 0).

Lemma pjw_wv_call : forall (W : world tfibsegs) ly S U regs mem md regs3 mem3 md3
  v pretty (t : PjTree.jv) D UL live peak cnt fail (Q : world tfibsegs -> config -> Prop),
  write_value_spec_at B tfibsegs 0 ->
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly S W (unpoison U mem3) md3 0 ->
  ARU tfibsegs B ly S U W mem3 md3 ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem3) ->
  spZ regs3 = spZ regs - FRAME_pj_write ->
  getr regs3 1 = w64 PJW_WV_RET ->
  getr regs3 3 = w64 (as_gp B) -> getr regs3 4 = w64 (as_tp B) ->
  getr regs3 8 = w64 pretty ->
  getr regs3 10 = w64 (spZ regs - 56) -> getr regs3 11 = w64 v -> getr regs3 12 = w64 pretty ->
  getr regs3 13 = w64 0 ->
  0 <= pretty < alloc_ceiling ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 56) 8 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 48) 8 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 40) 8 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 32) 4 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 16) 8 (s0Z regs) ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 8) 8 (raZ regs) ->
  fs_heads B ly S U -> Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  PjStruct.pj_node tfibsegs (mrestrict (w_H W) mem3) (fun a k => In (a, k) UL) v t D ->
  FSH_Fn_reader.pobj tfibsegs B ly S W mem3 v ->
  ublocks_ok B tfibsegs ly S W mem3 UL -> (forall a k, In (a, k) D -> In (a, k) UL) ->
  jv_plain t -> (PjTree.depth t <= 2)%nat ->
  fs_glob tfibsegs W mem3 live peak cnt fail ->
  Z.of_nat (length (concat (WriterValue.wvpieces t (negb (pretty =? 0)) 0))) + 1 <= WMAX ->
  wbudget_pre S 0 cnt live (pjw_st_wv t (negb (pretty =? 0)) cnt fail) ->
  (forall ly2 S2 (W2 : world tfibsegs) U2 regsE memE mdE buf',
     ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
       ly2 S2 W2 (unpoison U2 memE) mdE (0 + wevk 0 (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) ->
     ARU tfibsegs B ly2 S2 U2 W2 memE mdE ->
     st_ok tfibsegs (Ereg regsE (pjw_extra regs buf'
         (Z.of_nat (length (WriterApp.w_text (pjw_st_wv t (negb (pretty =? 0)) cnt fail))))
         (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail))))
       (fss_ret PJW_WV_RET 64 (pjw_cs_obj (WriterApp.w_failed (pjw_st_wv t (negb (pretty =? 0)) cnt fail))))
       (restrict (w_H W2) (YK11.mkst regsE (Z_to_bv 64 PJW_WV_RET) memE (YK11.seg_rom tfibsegs))) ->
     spZ regsE = spZ regs - FRAME_pj_write ->
     (forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regsE q = getr regs3 q) ->
     uswap U U2 0 buf' 0 ->
     wout_ok B tfibsegs ly2 S2 W2 memE (spZ regs - 56) buf'
       (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail))
       (WriterApp.w_failed (pjw_st_wv t (negb (pretty =? 0)) cnt fail))
       (WriterApp.w_text (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) ->
     wbudget_kept S S2 0 0 cnt (WriterApp.w_failed (pjw_st_wv t (negb (pretty =? 0)) cnt fail))
       (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail))
       (WriterApp.w_cnt (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) ->
     bswap (ablocks B ly S) (ablocks B ly2 S2) 0 buf' 0
       (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) ->
     PjStruct.pj_node tfibsegs (mrestrict (w_H W2) memE) (fun a k => In (a, k) UL) v t D ->
     (exists peak', peak <= peak' <= Z.max peak (live - 0 + WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) /\
        fs_glob tfibsegs W2 memE (live + WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail) - 0) peak'
          (WriterApp.w_cnt (pjw_st_wv t (negb (pretty =? 0)) cnt fail))
          (WriterApp.w_fail (pjw_st_wv t (negb (pretty =? 0)) cnt fail))) ->
     SRr tfibsegs W2 (cfg_at tfibsegs PJW_WV_RET regsE memE mdE) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_write_value regs3 mem3 md3) Q.
Proof.
intros W ly S U regs mem md regs3 mem3 md3 v pretty t D UL live peak cnt fail Q
  HWV HJ HARU HRO Hsp3 Hra3 Hgp3 Htp3 H8 H10 H11 H12 H13 Hpr Z0 Z1 Z2 Z3 V40 V48 V56
  HHEADS HFRL HNODE HPOBJ HUL HDUL HPLAIN HDEP HGLOB HlenM HBUD K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold pjw_st_wv in HBUD, K.
assert (Hsp3n : spZ regs3 = spZ regs - 64) by (rewrite Hsp3; reflexivity).
assert (HSTKv : 4160 <= STK_pj_write) by (vm_compute; discriminate).
pose proof HJ as (HARj & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HGLOB as (_ & _ & _ & _ & Hlive & _).
assert (Hra3' : raZ regs3 = PJW_WV_RET)
  by (unfold raZ; rewrite Hra3; unfold w64, PJW_WV_RET; apply unsigned_lit_small; lia).
assert (Hs03 : s0Z regs3 = pretty)
  by (unfold s0Z; rewrite H8; unfold w64; apply unsigned_lit_small; lia).
(* the callee's window is stack; the root's 56 bytes and every block of D lie below alloc_ceiling, so no byte of
   the tree's footprint is in [o, ot) *)
assert (HFOOT : forall x, spZ regs - 56 <= x < spZ regs - 16 -> ~ PjStruct.pj_foot v D x).
{ intros x Hx [Hroot | ((a, k) & Hin & Hh)].
  - destruct (FSW_rd.fsw_pobj_low B ly S W (unpoison U mem3) md3 mem3 v HARj HPOBJ) as (P1 & P2). lia.
  - unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
    destruct (FSW_rd.fsw_rblock_low B ly S W (unpoison U mem3) md3 mem3 a k HARj (HUL a k (HDUL a k Hin)))
      as (R1 & R2). lia. }
destruct (pjw_wv_premises W ly S U regs mem md regs3 mem3 md3 D UL HJ HARU HRO Hsp3 Hra3 Hgp3 Htp3
  ltac:(rewrite Hs03; lia) Z0 Z1 Z2 Z3 HUL HDUL)
  as (HPRE & HOUT0 & Hle56 & Hle32 & Hmod & Hlytop & HPRES & HDUL' & Hchain).
assert (Ewb : wbuf_fp 0 0 = @nil (Z * Z)) by reflexivity.
(* the callee's footprint beyond the statics is empty (cap = 0): every byte of it is an FS_PSTAT_FP image byte *)
assert (HFPS : fsw_fp_sub B ly S ly S [] FS_PSTAT_FP (FS_PSTAT_FP ++ wbuf_fp 0 0)).
{ intros a Ha. apply inFP_app in Ha as [Ha|Ha].
  - right; right; left. split; [exact Ha | exact (pjw_f_pstat_img a Ha)].
  - exfalso. rewrite Ewb in Ha. exact (inFP_nil a Ha). }
(* ---- write_value's premises at the call ---- *)
eapply SRr_bind.
{ eapply (HWV ly S U W regs3 mem3 md3 [] (spZ regs - 16) (spZ regs - 56) v pretty 0 t D UL 0 0 0 []
    live peak cnt fail).
  - exact HDEP.
  - exact HPRE.
  - exact HHEADS.
  - exact HFRL.
  - exact H10.
  - exact H11.
  - exact H12.
  - exact H13.
  - exact Hpr.
  - lia.
  - lia.
  - left. rewrite Hs03. lia.
  - exact HOUT0.
  - exact HGLOB.
  - intros Hc. exfalso. apply Hc. reflexivity.
  - exact Hle56.
  - exact Hle32.
  - exact Hmod.
  - exact Hlytop.
  - left. exact Hchain.
  - exact HPRES.
  - exact HNODE.
  - exact HPOBJ.
  - exact HUL.
  - exact HDUL'.
  - intros Hc. exfalso. apply Hc. reflexivity.
  - exact HPLAIN.
  - exact HFOOT.
  - cbn [length Z.of_nat]. lia.
  - unfold WMAX. lia.
  - lia.
  - exact HBUD. }
(* ---- write_value's post, composed back into the caller's journal ---- *)
cbv beta. intros W2 c2 Hwle (st' & buf' & U2 & Est & Husw & Hpost).
unfold wpost, fpostU in Hpost.
destruct Hpost as (ly2 & S2 & regsE & memE & mdE & Ec2 & HJc & OK2 & PO2 & HPRS & HOUT2 & HKEPT & HBSW & HWK &
  HNODE2 & HGL2).
subst c2. subst st'.
set (ST := WriterApp.putN (WriterApp.mkW 0 [] 0 cnt fail [])
             (WriterValue.wvpieces t (negb (pretty =? 0)) 0)) in *.
assert (HARU2 : ARU tfibsegs B ly2 S2 U2 W2 memE mdE)
  by (split; [exact (proj1 HJc) | split; [exact OK2 | exact PO2]]).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & Habove & _).
pose proof HOUT2 as (_ & _ & _ & _ & Hbufr3 & Hcapr3 & Vb3 & Vl3 & Vc3 & Vf3 & Hf013 & _ & Hdisj3).
assert (Hlenr3 : 0 <= Z.of_nat (length (WriterApp.w_text ST)) < 2 ^ 64).
{ destruct Hdisj3 as [(_ & _ & Ht0)|(_ & _ & Hlt & _)]; [rewrite Ht0; cbn [length Z.of_nat]; lia | lia]. }
(* the three saved words on the memory after the call: s1 inside the window from wkeep, s0 and ra above it *)
assert (V40' : val_mem tfibsegs (mrestrict (w_H W2) memE) (spZ regs - 24) 8 (bv_unsigned (getr regs 9))).
{ intros k Hk. rewrite (proj1 (HWK (spZ regs - 24 + Z.of_nat k) ltac:(lia) ltac:(lia))). exact (V40 k Hk). }
assert (KEEPUP : forall a, spZ regs - 16 <= a < spZ regs ->
  mrestrict (w_H W2) memE (Z_to_bv 64 a) = mrestrict (w_H W) mem3 (Z_to_bv 64 a)).
{ intros a Ha. apply (pjw_p_above_kept ly S U W mem3 md3 ly2 S2 U2 W2 memE mdE a HARU HARU2 ltac:(lia)).
  apply Habove; lia. }
assert (V48' : val_mem tfibsegs (mrestrict (w_H W2) memE) (spZ regs - 16) 8 (s0Z regs)).
{ intros k Hk. pose proof (V48 k Hk) as Hv. unfold mbyte in *.
  rewrite (KEEPUP (spZ regs - 16 + Z.of_nat k) ltac:(lia)). exact Hv. }
assert (V56' : val_mem tfibsegs (mrestrict (w_H W2) memE) (spZ regs - 8) 8 (raZ regs)).
{ intros k Hk. pose proof (V56 k Hk) as Hv. unfold mbyte in *.
  rewrite (KEEPUP (spZ regs - 8 + Z.of_nat k) ltac:(lia)). exact Hv. }
assert (CHK : Forall (YP09.chunk_ok tfibsegs (Ereg regsE (pjw_extra regs buf'
    (Z.of_nat (length (WriterApp.w_text ST))) (WriterApp.w_cap ST)))
    (mrestrict (w_H W2) memE) (spZ regs - 64)) (pjw_cs_obj (WriterApp.w_failed ST))).
{ unfold pjw_cs_obj. repeat constructor.
  - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 8 8%N (SOff 35 0) buf').
    + rewrite fsw_SOff0. change 35%nat with (32 + 3)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
      reflexivity.
    + cbn [Z.of_N]; lia.
    + cbn [Z.of_N]; lia.
    + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
      replace (spZ regs - 64 + 8) with (spZ regs - 56) by lia. exact Vb3.
  - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 16 8%N (SOff 36 0)
      (Z.of_nat (length (WriterApp.w_text ST)))).
    + rewrite fsw_SOff0. change 36%nat with (32 + 4)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
      reflexivity.
    + cbn [Z.of_N]; lia.
    + cbn [Z.of_N]; lia.
    + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
      replace (spZ regs - 64 + 16) with (spZ regs - 56 + 8) by lia. exact Vl3.
  - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 24 8%N (SOff 37 0) (WriterApp.w_cap ST)).
    + rewrite fsw_SOff0. change 37%nat with (32 + 5)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
      reflexivity.
    + cbn [Z.of_N]; lia.
    + cbn [Z.of_N]; lia.
    + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
      replace (spZ regs - 64 + 24) with (spZ regs - 56 + 16) by lia. exact Vc3.
  - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 32 4%N (SLit (WriterApp.w_failed ST))
      (WriterApp.w_failed ST)).
    + reflexivity.
    + cbn [Z.of_N]; lia.
    + cbn [Z.of_N]; lia.
    + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
      replace (spZ regs - 64 + 32) with (spZ regs - 56 + 24) by lia. exact Vf3.
  - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 40 8%N (SOff 34 0) (bv_unsigned (getr regs 9))).
    + rewrite fsw_SOff0. change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
      symmetry. apply Z_to_bv_bv_unsigned.
    + cbn [Z.of_N]. apply u64_range.
    + cbn [Z.of_N]; lia.
    + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
      replace (spZ regs - 64 + 40) with (spZ regs - 24) by lia. exact V40'.
  - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 48 8%N (SOff 33 0) (s0Z regs)).
    + rewrite fsw_SOff0. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
      unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned.
    + cbn [Z.of_N]. unfold s0Z. apply u64_range.
    + cbn [Z.of_N]; lia.
    + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
      replace (spZ regs - 64 + 48) with (spZ regs - 16) by lia. exact V48'.
  - apply (chunk_ok_val tfibsegs _ _ (spZ regs - 64) 56 8%N (SOff 32 0) (raZ regs)).
    + rewrite fsw_SOff0. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth pjw_extra].
      unfold raZ. symmetry. apply Z_to_bv_bv_unsigned.
    + cbn [Z.of_N]. unfold raZ. apply u64_range.
    + cbn [Z.of_N]; lia.
    + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
      replace (spZ regs - 64 + 56) with (spZ regs - 8) by lia. exact V56'. }
destruct (fsw_after_callFPU_ot B STK_pj_write (spZ regs) FS_PSTAT_FP [] ly S U W mem md W ly S U mem3 md3 0
  (STK_write_value 2) (FS_PSTAT_FP ++ wbuf_fp 0 0) (spZ regs - 16) 64 regs3 ly2 S2 U2 W2 regsE memE mdE _
  (pjw_extra regs buf' (Z.of_nat (length (WriterApp.w_text ST))) (WriterApp.w_cap ST))
  (pjw_cs_obj (WriterApp.w_failed ST)) PJW_WV_RET
  HJ HARU HJc HFPS OK2 PO2 HPRS ltac:(lia) ltac:(lia) ltac:(vm_compute; discriminate)
  ltac:(vm_compute; discriminate) ltac:(reflexivity) ltac:(lia) ltac:(lia)
  ltac:(vm_compute; reflexivity) CHK) as (HJ4 & HARU4 & HS4).
rewrite Hra3.
apply (K ly2 S2 W2 U2 regsE memE mdE buf').
- exact HJ4.
- exact HARU4.
- exact HS4.
- unfold spZ, FRAME_pj_write.
  rewrite (fsw_pres regs3 regsE 2%bv HPRS ltac:(unfold acallee_saved; left; reflexivity)). exact Hsp3n.
- intros q Hq. exact (fsw_pres regs3 regsE q HPRS Hq).
- exact Husw.
- exact HOUT2.
- exact HKEPT.
- exact HBSW.
- exact HNODE2.
- exact HGL2.
Qed.

(* ================= the closing composition (a Theorem Labs lane) ================= *)

Local Ltac pjw_c_proj :=
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls] in *.

(* ================= the writer-model facts pj_write's closing theorem composes =================
   st1 = the state after write_value from the zeroed object (calls start at []), pjw_rst st1 its fields with the
   calls reset (what put's spec starts from), st' = pj_write's own trace. Template for the monotonicity proofs: the
   bespoke line, a Theorem Labs lane's pj_write.v:211-232
   (pjw_put1_cap / pjw_putN_cap), same WriterApp model. *)
Definition pjw_rst (st : WriterApp.wst) : WriterApp.wst :=
  WriterApp.mkW (WriterApp.w_failed st) (WriterApp.w_text st) (WriterApp.w_cap st) (WriterApp.w_cnt st)
    (WriterApp.w_fail st) [].

(* a put only appends to the request trace, and what it appends does not depend on the trace so far *)
Lemma pjw_c_put1_calls : forall st b,
  WriterApp.w_calls (WriterApp.put1 st b) =
  WriterApp.w_calls st ++ WriterApp.w_calls (WriterApp.put1 (pjw_rst st) b).
Proof.
  intros [f t c n fl cs] b. unfold pjw_rst, WriterApp.put1. pjw_c_proj.
  destruct (negb (f =? 0)); [pjw_c_proj; rewrite app_nil_r; reflexivity|].
  destruct (_ <=? c); [pjw_c_proj; rewrite app_nil_r; reflexivity|].
  destruct (n =? fl); pjw_c_proj; reflexivity.
Qed.

Lemma pjw_c_putN_calls_len : forall P st,
  (length (WriterApp.w_calls st) <= length (WriterApp.w_calls (WriterApp.putN st P)))%nat.
Proof.
  induction P as [|b P IH]; intros st; [rewrite WriterApp.putN_nil; lia|].
  rewrite WriterApp.putN_cons. specialize (IH (WriterApp.put1 st b)).
  rewrite pjw_c_put1_calls, length_app in IH. lia.
Qed.

(* the trace invariant of a call that starts from cap = 0 with no request: no request means cap = 0, and a request
   that left cap = 0 was refused, so the state is failed *)
Definition pjw_c_inv (st : WriterApp.wst) : Prop :=
  0 <= WriterApp.w_cap st /\ (WriterApp.w_calls st = [] -> WriterApp.w_cap st = 0) /\
  (WriterApp.w_cap st = 0 -> WriterApp.w_calls st <> [] -> WriterApp.w_failed st <> 0).

Lemma pjw_c_inv_put1 : forall st b, pjw_c_inv st -> pjw_c_inv (WriterApp.put1 st b).
Proof.
  intros [f t c n fl cs] b (H0 & H1 & H2). pjw_c_proj.
  unfold WriterApp.put1. pjw_c_proj.
  destruct (f =? 0) eqn:Ef; cbn [negb].
  - apply Z.eqb_eq in Ef. subst f.
    destruct (_ <=? c).
    + unfold pjw_c_inv. pjw_c_proj. split; [exact H0|]. split; [exact H1 | exact H2].
    + destruct (n =? fl); unfold pjw_c_inv; pjw_c_proj.
      * split; [exact H0|]. split; [|intros _ _; discriminate].
        intros Hc. apply app_eq_nil in Hc as [_ Hc]. discriminate Hc.
      * pose proof (pjw_m_newcap_pos c (Z.of_nat (length t) + Z.of_nat (length b) + 1) H0) as Hp.
        split; [lia|]. split; [|intros Hc _; lia].
        intros Hc. apply app_eq_nil in Hc as [_ Hc]. discriminate Hc.
  - unfold pjw_c_inv. pjw_c_proj. split; [exact H0|]. split; [exact H1 | exact H2].
Qed.

Lemma pjw_c_inv_putN : forall P st, pjw_c_inv st -> pjw_c_inv (WriterApp.putN st P).
Proof.
  induction P as [|b P IH]; intros st H; [exact H|].
  rewrite WriterApp.putN_cons. apply IH. apply pjw_c_inv_put1. exact H.
Qed.

Lemma pjw_c_inv_init : forall cnt fail, pjw_c_inv (WriterApp.mkW 0 [] 0 cnt fail []).
Proof.
  intros cnt fail. unfold pjw_c_inv. pjw_c_proj. split; [lia|]. split; [reflexivity|].
  intros _ H. exfalso. exact (H eq_refl).
Qed.

(* pj_write's own count splits as write_value's at cap = 0 plus put's at the capacity write_value left *)
Lemma pjw_c_wev_split : forall st b, pjw_c_inv st ->
  wev0 (WriterApp.put1 st b) = wevk 0 st + wevk (WriterApp.w_cap st) (WriterApp.put1 (pjw_rst st) b).
Proof.
  intros st b (H0 & H1 & H2).
  pose proof (pjw_c_put1_calls st b) as E.
  unfold wevk, wev0, wcalls. rewrite E, Z.eqb_refl.
  destruct (WriterApp.w_calls st) as [|x r] eqn:Ec.
  - rewrite (H1 eq_refl), Z.eqb_refl. cbn [app]. lia.
  - destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [Hc0|Hc0].
    + assert (Hf : WriterApp.w_failed st <> 0) by (apply H2; [exact Hc0 | discriminate]).
      rewrite (pjw_put1_sticky (pjw_rst st) b) by (unfold pjw_rst; cbn [WriterApp.w_failed]; exact Hf).
      unfold pjw_rst. cbn [WriterApp.w_calls app]. rewrite app_nil_r. lia.
    + cbn [app]. rewrite length_app, Nat2Z.inj_add. unfold EV_fuzz_realloc. lia.
Qed.

Lemma pjw_c_wcalls_split : forall st b,
  wcalls (WriterApp.put1 st b) = wcalls st + wcalls (WriterApp.put1 (pjw_rst st) b).
Proof. intros st b. unfold wcalls. rewrite pjw_c_put1_calls, length_app. lia. Qed.

Lemma pjw_c_wevk_nonneg : forall c st, 0 <= wevk c st.
Proof.
  intros c st. unfold wevk, wev0, wcalls, EV_fuzz_malloc, EV_fuzz_realloc.
  destruct (c =? 0); [destruct (WriterApp.w_calls st)|]; lia.
Qed.

(* w_cnt counts the requests (no wrap under the budget premise) *)
Lemma pjw_c_put1_cnt : forall st b, 0 <= WriterApp.w_cnt st ->
  WriterApp.w_cnt st + Z.of_nat (length (WriterApp.w_calls (WriterApp.put1 (pjw_rst st) b))) < 2 ^ 64 ->
  WriterApp.w_cnt (WriterApp.put1 st b) =
  WriterApp.w_cnt st + Z.of_nat (length (WriterApp.w_calls (WriterApp.put1 (pjw_rst st) b))).
Proof.
  intros [f t c n fl cs] b. unfold pjw_rst, WriterApp.put1. pjw_c_proj. intros Hn.
  destruct (negb (f =? 0)); [pjw_c_proj; cbn [length Z.of_nat]; lia|].
  destruct (_ <=? c); [pjw_c_proj; cbn [length Z.of_nat]; lia|].
  destruct (n =? fl); pjw_c_proj; cbn [length app Z.of_nat Pos.of_succ_nat]; intros Hb;
    rewrite Z.mod_small by lia; lia.
Qed.

Lemma pjw_c_putN_cnt : forall P st, 0 <= WriterApp.w_cnt st ->
  WriterApp.w_cnt st + (Z.of_nat (length (WriterApp.w_calls (WriterApp.putN st P))) -
                        Z.of_nat (length (WriterApp.w_calls st))) < 2 ^ 64 ->
  WriterApp.w_cnt (WriterApp.putN st P) =
  WriterApp.w_cnt st + (Z.of_nat (length (WriterApp.w_calls (WriterApp.putN st P))) -
                        Z.of_nat (length (WriterApp.w_calls st))).
Proof.
  induction P as [|b P IH]; intros st Hn Hb; [rewrite WriterApp.putN_nil; lia|].
  rewrite WriterApp.putN_cons in *.
  pose proof (pjw_c_putN_calls_len P (WriterApp.put1 st b)) as L1.
  pose proof (pjw_c_put1_calls st b) as E1.
  assert (L2 : length (WriterApp.w_calls (WriterApp.put1 st b)) =
               (length (WriterApp.w_calls st) + length (WriterApp.w_calls (WriterApp.put1 (pjw_rst st) b)))%nat)
    by (rewrite E1, length_app; reflexivity).
  pose proof (pjw_c_put1_cnt st b Hn ltac:(lia)) as C1.
  rewrite (IH (WriterApp.put1 st b)); lia.
Qed.

Lemma pjw_c_put1_text_len : forall st b,
  (length (WriterApp.w_text (WriterApp.put1 st b)) <= length (WriterApp.w_text st) + length b)%nat.
Proof.
  intros [f t c n fl cs] b. unfold WriterApp.put1. pjw_c_proj.
  destruct (negb (f =? 0)); [pjw_c_proj; lia|].
  destruct (_ <=? c); [pjw_c_proj; rewrite length_app; lia|].
  destruct (n =? fl); pjw_c_proj; [lia | rewrite length_app; lia].
Qed.

Lemma pjw_c_putN_text_len : forall P st,
  (length (WriterApp.w_text (WriterApp.putN st P)) <= length (WriterApp.w_text st) + length (concat P))%nat.
Proof.
  induction P as [|b P IH]; intros st; [rewrite WriterApp.putN_nil; cbn [concat length]; lia|].
  rewrite WriterApp.putN_cons. cbn [concat]. rewrite length_app.
  pose proof (pjw_c_put1_text_len st b). specialize (IH (WriterApp.put1 st b)). lia.
Qed.

Lemma pjw_c_put1_cap : forall st b, 0 <= WriterApp.w_cap st ->
  WriterApp.w_cap st <= WriterApp.w_cap (WriterApp.put1 st b).
Proof.
  intros [f t c n fl cs] b Hc. pjw_c_proj. unfold WriterApp.put1. pjw_c_proj.
  destruct (negb (f =? 0)); [pjw_c_proj; lia|].
  destruct (_ <=? c); [pjw_c_proj; lia|].
  destruct (n =? fl); pjw_c_proj; [lia|].
  unfold WriterSpec.newcap. destruct (c =? 0) eqn:E.
  - apply Z.eqb_eq in E. pose proof (pjw_m_dbl_ge 64 4096 (Z.of_nat (length t) + Z.of_nat (length b) + 1)
      ltac:(lia)). lia.
  - apply Z.eqb_neq in E. exact (pjw_m_dbl_ge 64 c _ ltac:(lia)).
Qed.

(* ================= block and head lists ================= *)
(* a block appears once in the live list *)
Lemma pjw_c_blk_once : forall ly S (W : world tfibsegs) mem md C1 C2 p n,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = C1 ++ (p, n) :: C2 -> ~ In (p, n) (C1 ++ C2).
Proof.
  intros ly S W mem md C1 C2 p n HAR E Hin.
  pose proof (AR_laws_ok tfibsegs B) as LAWS.
  assert (Hx : In (p, n) (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks tfibsegs B LAWS ly S W mem md p n HAR Hx) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [Hr _].
  apply in_app_or in Hin as [Hin|Hin]; apply in_split in Hin as (l1 & l2 & El).
  - subst C1. pose proof (sep_blocks_pos tfibsegs B LAWS ly S W mem md (p, n) (p, n) l1 l2 C2 HAR
      ltac:(rewrite E, <- app_assoc; reflexivity)) as Hd.
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
  - subst C2. pose proof (sep_blocks_pos tfibsegs B LAWS ly S W mem md (p, n) (p, n) C1 l1 l2 HAR E) as Hd.
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma pjw_c_split_uniq : forall (x : Z * Z) l1 l2 C1 C2, ~ In x (C1 ++ C2) ->
  l1 ++ x :: l2 = C1 ++ x :: C2 -> l1 = C1 /\ l2 = C2.
Proof.
  intros x l1. induction l1 as [|a l1 IH]; intros l2 C1 C2 Hn E; destruct C1 as [|c C1]; cbn [app] in *.
  - injection E as E. split; [reflexivity | exact E].
  - injection E as E1 E2. subst c. exfalso. apply Hn. left. reflexivity.
  - injection E as E1 E2. subst a. exfalso. apply Hn. rewrite <- E2. apply in_or_app. right. left. reflexivity.
  - injection E as E1 E2. subst c.
    destruct (IH l2 C1 C2 ltac:(intros H; apply Hn; right; exact H) E2) as [-> ->]. split; reflexivity.
Qed.

(* the cap = 0 write leaves either nothing, or one new block anywhere in the list; the second call (put) at the
   capacity the first one left composes to the same shape (the C-lists of a realloc compose) *)
Lemma pjw_c_bswap_comp : forall ly S (W : world tfibsegs) mem md ly1 S1 (W1 : world tfibsegs) mem1 md1
  A2 buf1 cap1 buf2 cap2,
  AR tfibsegs B ly S W mem md -> AR tfibsegs B ly1 S1 W1 mem1 md1 ->
  (cap1 = 0 -> buf1 = 0) ->
  bswap (ablocks B ly S) (ablocks B ly1 S1) 0 buf1 0 cap1 -> bswap (ablocks B ly1 S1) A2 buf1 buf2 cap1 cap2 ->
  bswap (ablocks B ly S) A2 0 buf2 0 cap2.
Proof.
  intros ly S W mem md ly1 S1 W1 mem1 md1 A2 buf1 cap1 buf2 cap2 HAR HAR1 Hc1 H1 H2.
  assert (Hneg : forall l ly' S' (W' : world tfibsegs) mem' md' C1 C2, AR tfibsegs B ly' S' W' mem' md' ->
    l = ablocks B ly' S' -> l = C1 ++ (0 - HEAD, 0 + HEAD) :: C2 -> False).
  { intros l ly' S' W' mem' md' C1 C2 HA El E.
    assert (Hin : In (0 - HEAD, 0 + HEAD) (ablocks B ly' S'))
      by (rewrite <- El, E; apply in_or_app; right; left; reflexivity).
    destruct (fsw_ablock_low B ly' S' W' mem' md' _ _ HA Hin) as (H4 & _). unfold HEAD in H4. lia. }
  destruct H1 as [(Eb1 & Ec1 & EA)|[(_ & C1 & C2 & EA & EC)|(X1 & X2 & _ & _ & EX & _)]];
    [| | exfalso; exact (Hneg _ ly S W mem md X1 X2 HAR eq_refl EX)].
  - (* nothing was allocated: the list, buf and cap are unchanged *)
    subst buf1 cap1. rewrite EA in H2.
    destruct H2 as [(Eb2 & Ec2 & EA2)|[(_ & D1 & D2 & EA2 & ED)|(X1 & X2 & _ & _ & EX & _)]];
      [| | exfalso; exact (Hneg _ ly S W mem md X1 X2 HAR eq_refl EX)].
    + left. split; [exact Eb2|]. split; [exact Ec2 | exact EA2].
    + right. left. split; [reflexivity|]. exists D1, D2. split; [exact EA2 | exact ED].
  - (* one block b1 was taken, anywhere: ablocks1 = C1 ++ b1 :: C2 with C1 ++ C2 = ablocks *)
    assert (Hnot : ~ In (buf1 - HEAD, cap1 + HEAD) (C1 ++ C2))
      by exact (pjw_c_blk_once ly1 S1 W1 mem1 md1 C1 C2 _ _ HAR1 EA).
    destruct H2 as [(Eb2 & Ec2 & EA2)|[(Ec0 & D1 & D2 & EA2 & ED)|(X1 & X2 & D1 & D2 & EX & EA2 & ED)]].
    + right. left. split; [reflexivity|]. exists C1, C2. subst buf2 cap2. rewrite EA2. split; [exact EA | exact EC].
    + (* cap1 = 0 means buf1 = 0, and then b1 = (0 - HEAD, 0 + HEAD) is not a live block *)
      exfalso. pose proof (Hc1 Ec0) as Eb0. subst cap1 buf1.
      exact (Hneg _ ly1 S1 W1 mem1 md1 C1 C2 HAR1 eq_refl EA).
    + rewrite EA in EX. destruct (pjw_c_split_uniq _ X1 X2 C1 C2 Hnot (eq_sym EX)) as [-> ->].
      right. left. split; [reflexivity|]. exists D1, D2. split; [exact EA2|]. rewrite ED. exact EC.
Qed.

(* a range sits once in a pairwise-disjoint list of non-empty ranges *)
Lemma pjw_c_pw_dup : forall (h : Z * Z) l1 l2, pairwise zdisjoint (l1 ++ h :: l2) -> In h l2 -> 0 < snd h -> False.
Proof.
  intros h l1. induction l1 as [|a l1 IH]; intros l2 HP Hin Hpos; cbn [app pairwise] in HP.
  - destruct HP as (F & _). pose proof (proj1 (Forall_forall _ _) F h Hin) as Hd.
    unfold zdisjoint in Hd. lia.
  - exact (IH l2 (proj2 HP) Hin Hpos).
Qed.

(* the heads compose the same way (append form: the new head is the last one) *)
Lemma pjw_c_uswap_comp : forall U U1 U2 buf1 cap1 buf2,
  (forall V1 V2, U = V1 ++ (0 - HEAD, HEAD) :: V2 -> False) ->
  (forall V1 V2, U1 = V1 ++ (0 - HEAD, HEAD) :: V2 -> False) ->
  pairwise zdisjoint U1 -> (cap1 = 0 -> buf1 = 0) ->
  uswap U U1 0 buf1 0 -> uswap U1 U2 buf1 buf2 cap1 -> uswap U U2 0 buf2 0.
Proof.
  intros U U1 U2 buf1 cap1 buf2 Hneg0 Hneg1 HP Hc1 H1 H2.
  destruct H1 as [(EU & Eb)|[(V1 & V2 & EV & _)|(_ & EU)]]; [| exfalso; exact (Hneg0 V1 V2 EV) |].
  - subst U1 buf1. destruct H2 as [(EU2 & Eb2)|[(W1 & W2 & EW & EU2)|(_ & EU2)]].
    + left. split; [exact EU2 | exact Eb2].
    + right. left. exists W1, W2. split; [exact EW | exact EU2].
    + right. right. split; [reflexivity | exact EU2].
  - (* write_value took the first buffer: U1 = U ++ [h1] *)
    destruct H2 as [(EU2 & Eb2)|[(W1 & W2 & EW & EU2)|(Ec0 & EU2)]].
    + right. right. split; [reflexivity|]. subst U2 buf2. exact EU.
    + right. right. split; [reflexivity|].
      assert (Hnot : ~ In (buf1 - HEAD, HEAD) U).
      { intros Hin. apply in_split in Hin as (l1 & l2 & El). subst U1. rewrite El in HP.
        rewrite <- app_assoc in HP. cbn [app] in HP.
        apply (pjw_c_pw_dup (buf1 - HEAD, HEAD) l1 (l2 ++ [(buf1 - HEAD, HEAD)]) HP);
          [apply in_or_app; right; left; reflexivity | cbn [snd]; unfold HEAD; lia]. }
      rewrite EU in EW. destruct (pjw_app_last _ U W1 W2 _ Hnot EW) as [-> ->]. exact EU2.
    + exfalso. pose proof (Hc1 Ec0) as Eb0. subst buf1. exact (Hneg1 U [] EU).
Qed.


(* ================= footprint and statics facts for the closing composition ================= *)
(* fs's alloc.c statics are no read-only byte *)
Lemma pjw_c_pstat_not_ro : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
  intros a Hro (r & Hin & Hra).
  destruct Hro as [(s & Hs & Hw & Hr) | Hr].
  - assert (Hb : forallb (fun s => seg_writable s || forallb (fun r =>
        (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? fst r) || (snd r <=? Z.of_N (seg_base s))) FS_PSTAT_FP)
        tfibsegs = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hb. specialize (Hb s Hs). rewrite Hw in Hb. cbn [orb] in Hb.
    rewrite forallb_forall in Hb. specialize (Hb r Hin).
    apply orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
  - unfold FS_PSTAT_FP in Hin. unfold FS_RLO, FS_RHI in Hr. cbv [In] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hra; lia|]). destruct Hin.
Qed.

(* the statics lie below the shadow region *)
Lemma pjw_c_pstat_low : forall x, inFP FS_PSTAT_FP x -> x < kLowShadowBeg \/ kHighShadowEnd <= x.
Proof.
  intros x (r & Hin & Hx). left. unfold kLowShadowBeg.
  unfold FS_PSTAT_FP in Hin. cbv [In] in Hin.
  repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hx; lia|]). destruct Hin.
Qed.

(* the tree's footprint is no static byte: it is off the image (a live frame or block), the statics are on it *)
Lemma pjw_c_foot_not_pstat : forall ly S (W : world tfibsegs) mx md m v D UL,
  AR tfibsegs B ly S W mx md -> FSH_Fn_reader.pobj tfibsegs B ly S W m v -> ublocks_ok B tfibsegs ly S W m UL ->
  (forall a k, In (a, k) D -> In (a, k) UL) ->
  forall x, PjStruct.pj_foot v D x -> ~ inFP FS_PSTAT_FP x.
Proof.
  intros ly S W mx md m v D UL HAR HP HUL HD x Hf Hx.
  pose proof (pjw_f_pstat_img x Hx) as Hi. pose proof (AR_laws_ok tfibsegs B) as LAWS.
  destruct Hf as [Hv | ((a0 & kk) & Hb & Hh)].
  - exact (pjw_t_pobj_img ly S W mx md m v HAR HP x Hv Hi).
  - unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
    destruct (HUL a0 kk (HD a0 kk Hb)) as (Hin & _ & Hk & _).
    pose proof (req_size_pos (kk + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr).
    apply (blk_img tfibsegs B LAWS ly S W mx md (a0 - HEAD) (kk + HEAD) x HAR Hin); [unfold HEAD in *; lia | exact Hi].
Qed.

(* nor is a head byte of a block of the live list *)
Lemma pjw_c_ul_not_pstat : forall ly S (W : world tfibsegs) mx md m UL, AR tfibsegs B ly S W mx md ->
  ublocks_ok B tfibsegs ly S W m UL ->
  forall a kk i, In (a, kk) UL -> 0 <= i < 8 -> ~ inFP FS_PSTAT_FP (a - HEAD + i).
Proof.
  intros ly S W mx md m UL HAR HUL a kk i Hak Hi Hx. pose proof (AR_laws_ok tfibsegs B) as LAWS.
  destruct (HUL a kk Hak) as (Hin & _ & Hk & _).
  pose proof (req_size_pos (kk + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr).
  apply (blk_img tfibsegs B LAWS ly S W mx md (a - HEAD) (kk + HEAD) (a - HEAD + i) HAR Hin);
    [unfold HEAD in *; lia | exact (pjw_f_pstat_img _ Hx)].
Qed.

(* a write from cap = 0 keeps every block that was live before it *)
Lemma pjw_c_bswap0_keep : forall ly S (W : world tfibsegs) mx md A2 buf cap,
  AR tfibsegs B ly S W mx md -> bswap (ablocks B ly S) A2 0 buf 0 cap ->
  forall x, In x (ablocks B ly S) -> In x A2.
Proof.
  intros ly S W mx md A2 buf cap HAR H x Hx.
  destruct H as [(_ & _ & EA)|[(_ & C1 & C2 & EA & EC)|(X1 & X2 & _ & _ & EX & _)]].
  - rewrite EA. exact Hx.
  - rewrite EA. rewrite <- EC in Hx.
    apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx].
  - exfalso.
    assert (Hin : In (0 - HEAD, 0 + HEAD) (ablocks B ly S)) by (rewrite EX; apply in_or_app; right; left; reflexivity).
    destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin) as (H4 & _). unfold HEAD in H4. lia.
Qed.

(* a post's journal count may be raised *)
Lemma pjw_c_fpostU_k : forall STK sp0 FP regs ly S U (W : world tfibsegs) mem md k k' U' Q W' c',
  fpostU tfibsegs B STK sp0 FP regs ly S U W mem md k U' Q W' c' -> k <= k' ->
  fpostU tfibsegs B STK sp0 FP regs ly S U W mem md k' U' Q W' c'.
Proof.
  intros STK sp0 FP regs ly S U W mem md k k' U' Q W' c' (ly' & S' & regs' & mem' & md' & Ec & HJ & R) Hk.
  exists ly', S', regs', mem', md'. split; [exact Ec|]. split; [|exact R].
  eapply ajournal_mono_k; [exact HJ | exact Hk].
Qed.


(* the part of the object's state the return composition reads: below alloc_ceiling (the buffer block and its
   bytes) or plain numbers, so it survives a run that keeps only the memory below alloc_ceiling *)
Definition pjw_obj_data (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
    (buf cap failed : Z) (text : list Z) : Prop :=
  (failed = 0 \/ failed = 1) /\ 0 <= buf < 2 ^ 64 /\ 0 <= cap < 2 ^ 64 /\
  ((cap = 0 /\ buf = 0 /\ text = []) \/
   ((exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) /\ fs_rblock tfibsegs B ly S W mem buf cap /\
    Z.of_nat (length text) < cap /\ zbytes_at tfibsegs W mem buf (text ++ [0]))).

Lemma pjw_c_obj_data_of_wout : forall ly S (W : world tfibsegs) mem o buf cap failed text,
  wout_ok B tfibsegs ly S W mem o buf cap failed text -> pjw_obj_data ly S W mem buf cap failed text.
Proof.
  intros ly S W mem o buf cap failed text (_ & _ & _ & _ & Hb & Hc & _ & _ & _ & _ & Hf & _ & Hd).
  split; [exact Hf|]. split; [exact Hb|]. split; [exact Hc | exact Hd].
Qed.

Lemma pjw_c_obj_data_avb : forall ly S (W : world tfibsegs) mx md m m' buf cap failed text,
  AR tfibsegs B ly S W mx md -> pjw_avb W m m' ->
  pjw_obj_data ly S W m buf cap failed text -> pjw_obj_data ly S W m' buf cap failed text.
Proof.
  intros ly S W mx md m m' buf cap failed text HAR AV (Hf & Hb & Hc & Hd).
  split; [exact Hf|]. split; [exact Hb|]. split; [exact Hc|].
  destruct Hd as [H0|(Hp & Hrb & Hlt & Hz)]; [left; exact H0|right].
  destruct (fsw_rblock_low B ly S W mx md m buf cap HAR Hrb) as (H1 & H2).
  split; [exact Hp|]. split; [exact (pjw_rblock_avb ly S W m m' mx md buf cap HAR AV Hrb)|].
  split; [exact Hlt|].
  apply (pjw_p_zbytes_avb W m m' buf _ AV); [unfold HEAD in *; lia | rewrite length_app; cbn [length]; lia | exact Hz].
Qed.

(* the four statics cells start above 0, so a journal over FS_PSTAT_FP keeps the sink head *)
Lemma pjw_c_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof.
  apply sink_closed_pos. apply Forall_forall. intros r Hr. cbv [FS_PSTAT_FP In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [cbn [fst]; lia|]). destruct Hr.
Qed.

(* the read-only view at a later state, from the entry's, across the composite journal *)
Lemma pjw_c_arodata_at : forall ly S U (W : world tfibsegs) regs mem md ly2 S2 U2 (W2 : world tfibsegs) mem2 md2 k,
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) mem2).
Proof.
  intros ly S U W regs mem md ly2 S2 U2 W2 mem2 md2 k HJ HARU HARU2 HRO.
  exact (pjw_j_arodata_journalU STK_pj_write (spZ regs) FS_PSTAT_FP ly S U W mem md [] ly2 S2 U2 W2 mem2 md2 k
    HJ HARU HARU2 pjw_c_pstat_not_ro (fun a _ => fp_spares_closed FS_PSTAT_FP a pjw_c_pstat_closed) HRO).
Qed.

(* no user-poisoned range starts at 0 - HEAD: every range lies in a live block, which starts at 4096 or above *)
Lemma pjw_c_noneg_U : forall ly S U (W : world tfibsegs) mx md, AR tfibsegs B ly S W mx md -> upoison_ok B ly S U ->
  forall V1 V2, U = V1 ++ (0 - HEAD, HEAD) :: V2 -> False.
Proof.
  intros ly S U W mx md HAR (F & _) V1 V2 E.
  assert (Hin : In (0 - HEAD, HEAD) U) by (rewrite E; apply in_or_app; right; left; reflexivity).
  destruct (proj1 (Forall_forall _ _) F _ Hin) as (_ & _ & _ & p & n & Hp & Hle & _).
  destruct (fsw_ablock_low B ly S W mx md p n HAR Hp) as (H4 & _). cbn [fst] in Hle. unfold HEAD in Hle. lia.
Qed.

(* the heads after a cap = 0 write: the entry's, plus the new buffer's when one was taken *)
Lemma pjw_c_heads0 : forall ly S U (W : world tfibsegs) mx md ly2 S2 U2 (W2 : world tfibsegs) mx2 md2 buf cap,
  AR tfibsegs B ly S W mx md -> fs_heads B ly S U -> AR tfibsegs B ly2 S2 W2 mx2 md2 -> upoison_ok B ly2 S2 U2 ->
  uswap U U2 0 buf 0 -> bswap (ablocks B ly S) (ablocks B ly2 S2) 0 buf 0 cap -> (cap = 0 -> buf = 0) ->
  (cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly2 S2)) -> 0 <= cap ->
  fs_heads B ly2 S2 U2.
Proof.
  intros ly S U W mx md ly2 S2 U2 W2 mx2 md2 buf cap HAR HH HAR2 OK2 HUS HBS Hc0 Hin Hcap r Hr.
  assert (Hold : forall r0, In r0 U -> snd r0 = 16 /\ exists m, In (fst r0, m) (ablocks B ly2 S2) /\ 16 <= req_size m).
  { intros r0 Hr0. destruct (HH r0 Hr0) as (Hs & m & Hm & Hq). split; [exact Hs|]. exists m.
    split; [exact (pjw_c_bswap0_keep ly S W mx md _ buf cap HAR HBS _ Hm) | exact Hq]. }
  destruct HUS as [(EU & _)|[(V1 & V2 & EV & _)|(_ & EU)]].
  - rewrite EU in Hr. exact (Hold r Hr).
  - exfalso. destruct (HH (0 - HEAD, HEAD) ltac:(rewrite EV; apply in_or_app; right; left; reflexivity))
      as (_ & m0 & Hm0 & _).
    destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hm0) as (H4 & _). cbn [fst] in H4. unfold HEAD in H4. lia.
  - rewrite EU in Hr. apply in_app_or in Hr as [Hr|[<-|[]]]; [exact (Hold r Hr)|].
    destruct (Z.eq_dec cap 0) as [E0|E0].
    + exfalso. pose proof (Hc0 E0) as Eb. rewrite Eb in EU.
      exact (pjw_c_noneg_U ly2 S2 U2 W2 mx2 md2 HAR2 OK2 U [] EU).
    + split; [reflexivity|]. exists (cap + HEAD). split; [exact (Hin E0)|].
      unfold req_size. destruct (Z.eqb_spec (cap + HEAD) 0); unfold HEAD in *; lia.
Qed.

(* the footprint a put after a cap = 0 write may change: the statics, and the buffer that write took *)
Lemma pjw_c_fpsub_buf : forall ly S (W : world tfibsegs) mx md ly2 S2 (W2 : world tfibsegs) mx2 md2 buf cap,
  AR tfibsegs B ly S W mx md -> AR tfibsegs B ly2 S2 W2 mx2 md2 ->
  bswap (ablocks B ly S) (ablocks B ly2 S2) 0 buf 0 cap -> 0 <= cap ->
  (cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly2 S2)) ->
  fsw_fp_sub B ly S ly2 S2 [] FS_PSTAT_FP (FS_PSTAT_FP ++ wbuf_fp buf cap).
Proof.
  intros ly S W mx md ly2 S2 W2 mx2 md2 buf cap HAR HAR2 HBS Hcap Hin a Ha.
  apply inFP_app in Ha as [Ha|Ha].
  - right; right; left. split; [exact Ha | exact (pjw_f_pstat_img a Ha)].
  - unfold wbuf_fp in Ha. destruct (Z.eqb_spec cap 0) as [E0|E0]; [exfalso; exact (inFP_nil a Ha)|].
    right; left. destruct Ha as (r & Hr & Hra). cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Hra.
    exists (buf - HEAD), (cap + HEAD). split; [exact (Hin E0)|]. split.
    + intros Hold.
      destruct HBS as [(Eb & Ec & _)|[(_ & C1 & C2 & EA & EC)|(X1 & X2 & _ & _ & EX & _)]].
      * exact (E0 Ec).
      * apply (pjw_c_blk_once ly2 S2 W2 mx2 md2 C1 C2 _ _ HAR2 EA). rewrite EC. exact Hold.
      * assert (Hin0 : In (0 - HEAD, 0 + HEAD) (ablocks B ly S))
          by (rewrite EX; apply in_or_app; right; left; reflexivity).
        destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin0) as (H4 & _). unfold HEAD in H4. lia.
    + unfold req_size. destruct (Z.eqb_spec (cap + HEAD) 0); unfold HEAD in *; lia.
Qed.

(* pj_write's own trace against write_value's: with pretty, one more put of the newline *)
Lemma pjw_c_doc_true : forall t p cnt fail, p = true ->
  WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p) = WriterApp.put1 (pjw_st_wv t p cnt fail) [10].
Proof. intros t p cnt fail ->. rewrite pjw_putN_doc. reflexivity. Qed.

Lemma pjw_c_doc_false : forall t p cnt fail, p = false ->
  WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p) = pjw_st_wv t p cnt fail.
Proof. intros t p cnt fail ->. rewrite pjw_putN_doc. reflexivity. Qed.

Lemma pjw_c_inv_wv : forall t p cnt fail, pjw_c_inv (pjw_st_wv t p cnt fail).
Proof. intros t p cnt fail. unfold pjw_st_wv. apply pjw_c_inv_putN, pjw_c_inv_init. Qed.

Lemma pjw_c_st_rel : forall t p cnt fail,
  wevk 0 (pjw_st_wv t p cnt fail) <= wev0 (WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) /\
  WriterApp.w_cap (pjw_st_wv t p cnt fail) <=
    WriterApp.w_cap (WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) /\
  wcalls (pjw_st_wv t p cnt fail) <= wcalls (WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)).
Proof.
  intros t p cnt fail. pose proof (pjw_c_inv_wv t p cnt fail) as HI.
  destruct p.
  - rewrite (pjw_c_doc_true t true cnt fail eq_refl).
    rewrite (pjw_c_wev_split _ [10] HI), (pjw_c_wcalls_split _ [10]).
    pose proof (pjw_c_wevk_nonneg (WriterApp.w_cap (pjw_st_wv t true cnt fail))
      (WriterApp.put1 (pjw_rst (pjw_st_wv t true cnt fail)) [10])).
    pose proof (pjw_c_put1_cap (pjw_st_wv t true cnt fail) [10] (proj1 HI)).
    assert (0 <= wcalls (WriterApp.put1 (pjw_rst (pjw_st_wv t true cnt fail)) [10])) by (unfold wcalls; lia).
    lia.
  - rewrite (pjw_c_doc_false t false cnt fail eq_refl). unfold wevk. cbn [Z.eqb]. lia.
Qed.

(* write_value's request count is its trace's: cnt rises by one per request *)
Lemma pjw_c_cnt_wv : forall t p cnt fail, 0 <= cnt ->
  cnt + wcalls (pjw_st_wv t p cnt fail) < 2 ^ 64 ->
  WriterApp.w_cnt (pjw_st_wv t p cnt fail) = cnt + wcalls (pjw_st_wv t p cnt fail).
Proof.
  intros t p cnt fail Hc Hb. unfold pjw_st_wv, wcalls in *.
  rewrite (pjw_c_putN_cnt _ (WriterApp.mkW 0 [] 0 cnt fail [])); cbn [WriterApp.w_cnt WriterApp.w_calls length Z.of_nat];
    lia.
Qed.

Lemma pjw_c_wdoc_len_true : forall t p, p = true ->
  Z.of_nat (length (WriterValue.wdoc t p)) = Z.of_nat (length (concat (WriterValue.wvpieces t p 0))) + 1.
Proof. intros t p ->. rewrite pjw_wdoc_split, length_app. cbn [length]. lia. Qed.

Lemma pjw_c_wdoc_len : forall t p,
  Z.of_nat (length (concat (WriterValue.wvpieces t p 0))) <= Z.of_nat (length (WriterValue.wdoc t p)).
Proof. intros t p. rewrite pjw_wdoc_split, length_app. lia. Qed.

(* ================= the return composition: from PJW_PUT_RET to pj_write_spec's post =================
   At PJW_PUT_RET the object holds the final writer fields (buf, cap, failed, text = pj_write's own trace st');
   the composite head / block shapes from the entry are uswap / bswap at cap = 0. The three ends: failed = 0 returns
   buf (pjw_epi_success), failed = 1 with buf = 0 returns NULL (pjw_epi_failed_null), failed = 1 with a buffer frees
   it and returns NULL (pjw_epi_failed_block). The tree, the root and the live list ride across the composite journal
   from the entry (pjw_pj_node_journal / pjw_pobj_journal / pjw_ublocks_journal), the statics FP missing the
   footprint. *)
Lemma pjw_close_tail : forall (W : world tfibsegs) ly S U regs mem md ch v pretty (t : PjTree.jv) D UL live peak
    cnt fail ly2 S2 U2 (W2 : world tfibsegs) regs2 mem2 md2 k2 bufF capF failedF textF peakF,
  afn_preU tfibsegs B STK_pj_write ly S U W regs mem md ch -> fs_heads B ly S U ->
  PjStruct.pj_node tfibsegs (mrestrict (w_H W) mem) (fun a k => In (a, k) UL) v t D ->
  FSH_Fn_reader.pobj tfibsegs B ly S W mem v -> ublocks_ok B tfibsegs ly S W mem UL ->
  (forall a k, In (a, k) D -> In (a, k) UL) -> 0 <= live ->
  fuzz_free_spec tfibsegs B ->
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 mem2) md2 k2 ->
  k2 <= wev0 (WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0)))) ->
  st_nev S + wev0 (WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0))))
    + EV_fuzz_free <= EV_MAX ->
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 ->
  st_ok tfibsegs (Ereg regs2 (pjw_extra regs bufF (Z.of_nat (length textF)) capF))
    (fss_ret PJW_PUT_RET 64 (pjw_cs_obj failedF))
    (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 PJW_PUT_RET) mem2 (YK11.seg_rom tfibsegs))) ->
  spZ regs2 = spZ regs - 64 ->
  (forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 2 -> bv_unsigned q <> 8 ->
     bv_unsigned q <> 9 -> getr regs2 q = getr regs q) ->
  getr regs2 8 = w64 pretty -> 0 <= pretty < alloc_ceiling ->
  pjw_obj_data ly2 S2 W2 mem2 bufF capF failedF textF ->
  failedF = WriterApp.w_failed (WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0)))) ->
  capF = WriterApp.w_cap (WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0)))) ->
  (failedF = 0 -> textF = WriterValue.wdoc t (negb (pretty =? 0))) ->
  fs_glob tfibsegs W2 mem2 (live + capF) peakF
    (WriterApp.w_cnt (WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0)))))
    (WriterApp.w_fail (WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0))))) ->
  peak <= peakF <= Z.max peak (live + 2 * capF) ->
  fs_heads B ly2 S2 U2 -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) mem2) ->
  uswap U U2 0 bufF 0 -> bswap (ablocks B ly S) (ablocks B ly2 S2) 0 bufF 0 capF ->
  SRr tfibsegs W2 (cfg_at tfibsegs PJW_PUT_RET regs2 mem2 md2)
    (fun W' c' =>
       let st' := WriterApp.putN (WriterApp.w0 cnt fail)
                    (WriterValue.wdpieces t (negb (pretty =? 0))) in
       (exists q, WriterApp.w_failed st' = 0 /\
        fpostU tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP regs ly S U W mem md (wev0 st')
          (U ++ [(q - HEAD, HEAD)])
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 q /\
             pjw_succ B tfibsegs ly' S' W' mem' q t (negb (pretty =? 0)) (WriterApp.w_cap st') /\
             (exists C1 C2, ablocks B ly' S' = C1 ++ (q - HEAD, WriterApp.w_cap st' + HEAD) :: C2 /\
                C1 ++ C2 = ablocks B ly S) /\
             PjStruct.pj_node tfibsegs (mrestrict (w_H W') mem') (fun a k => In (a, k) UL) v t D /\
             (exists peak', peak <= peak' <= Z.max peak (live + 2 * WriterApp.w_cap st') /\
                fs_glob tfibsegs W' mem' (live + WriterApp.w_cap st') peak'
                  (WriterApp.w_cnt st') (WriterApp.w_fail st'))) W' c')
       \/
       (WriterApp.w_failed st' <> 0 /\
        fpostU tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP regs ly S U W mem md (wev0 st' + EV_fuzz_free) U
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 0 /\
             Permutation (ablocks B ly' S') (ablocks B ly S) /\
             PjStruct.pj_node tfibsegs (mrestrict (w_H W') mem') (fun a k => In (a, k) UL) v t D /\
             (exists peak', peak <= peak' <= Z.max peak (live + 2 * WriterApp.w_cap st') /\
                fs_glob tfibsegs W' mem' live peak' (WriterApp.w_cnt st') (WriterApp.w_fail st'))) W' c')).
Proof.
intros W ly S U regs mem md ch v pretty t D UL live peak cnt fail ly2 S2 U2 W2 regs2 mem2 md2 k2
  bufF capF failedF textF peakF HAPU HHEADS HNODE HPOBJ HUL HDUL Hlive0 HFF HJ2 Hk2 HEV HARU2 HS Hsp2 Hcs
  H8 Hpr HOUT Ef Ec Htext HGL HPEAK HH2 HRO2 HUS HBS.
set (st' := WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0)))) in *.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (K1 & K2 & K3 & K4 & K5).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HAPU) as HARU.
pose proof HAPU as ((HAR & Hra & Hra4 & Hgp & Htp & _) & _ & _).
pose proof HOUT as (Hf01 & Hbufr & Hcapr & Hdisj).
pose proof (pjw_c_foot_not_pstat ly S W _ md mem v D UL HAR HPOBJ HUL HDUL) as HFOOT.
assert (HLIVE2 : forall b n x, In (b, n) (ablocks B ly S) -> b <= x < b + req_size n -> PjStruct.pj_foot v D x ->
    In (b, n) (ablocks B ly2 S2))
  by (intros b n x Hb _ _; exact (pjw_c_bswap0_keep ly S W _ md _ bufF capF HAR HBS _ Hb)).
assert (Hs0 : 0 <= s0Z regs2 < alloc_ceiling)
  by (unfold s0Z; rewrite H8; unfold w64; rewrite unsigned_lit_small by lia; lia).
(* no head of U sits at 0 - HEAD, and no live block at state 2 starts there *)
assert (HnegU : forall V1 V2, U = V1 ++ (0 - HEAD, HEAD) :: V2 -> False).
{ intros V1 V2 EV.
  destruct (HHEADS (0 - HEAD, HEAD) ltac:(rewrite EV; apply in_or_app; right; left; reflexivity))
    as (_ & m0 & Hm0 & _).
  destruct (fsw_ablock_low B ly S W _ md _ _ HAR Hm0) as (H4 & _). cbn [fst] in H4. unfold HEAD in H4. lia. }
assert (HnegA : forall X1 X2, ablocks B ly S = X1 ++ (0 - HEAD, 0 + HEAD) :: X2 -> False).
{ intros X1 X2 EX.
  assert (Hin : In (0 - HEAD, 0 + HEAD) (ablocks B ly S)) by (rewrite EX; apply in_or_app; right; left; reflexivity).
  destruct (fsw_ablock_low B ly S W _ md _ _ HAR Hin) as (H4 & _). unfold HEAD in H4. lia. }
destruct Hf01 as [Hf0|Hf1].
- (* ---- success: failed = 0, the buffer is returned ---- *)
  rewrite Hf0 in HS, Htext. pose proof (Htext eq_refl) as Etx. subst textF.
  assert (Hcap0 : capF <> 0).
  { rewrite Ec. apply pjw_putN_cap_pos; [|exact (eq_trans (eq_sym Ef) Hf0)].
    intros E. unfold WriterValue.wdpieces in E. apply app_eq_nil in E as [E _]. exact (pjw_wvpieces_cons _ _ _ E). }
  destruct Hdisj as [(Hc00 & _ & _)|(Hpow & Hrb & Hlt & Hz)]; [exfalso; exact (Hcap0 Hc00)|].
  destruct (fsw_rblock_low B ly2 S2 W2 _ md2 mem2 bufF capF (proj1 HARU2) Hrb) as (Hb1 & Hb2).
  assert (EU2 : U2 = U ++ [(bufF - HEAD, HEAD)]).
  { destruct HUS as [(_ & Eb)|[(V1 & V2 & EV & _)|(_ & EU)]];
      [unfold HEAD in Hb1; lia | exfalso; exact (HnegU V1 V2 EV) | exact EU]. }
  assert (EBS : exists C1 C2, ablocks B ly2 S2 = C1 ++ (bufF - HEAD, capF + HEAD) :: C2 /\ C1 ++ C2 = ablocks B ly S).
  { destruct HBS as [(Eb & _ & _)|[(_ & C1 & C2 & EA & EC)|(X1 & X2 & _ & _ & EX & _)]].
    - unfold HEAD in Hb1. lia.
    - exists C1, C2. split; [exact EA | exact EC].
    - exfalso. exact (HnegA X1 X2 EX). }
  assert (HN2 : PjStruct.pj_node tfibsegs (mrestrict (w_H W2) mem2) (fun a k => In (a, k) UL) v t D)
    by exact (pjw_pj_node_journal STK_pj_write (spZ regs) FS_PSTAT_FP ly S U W mem md [] ly2 S2 U2 W2 mem2 md2 k2
                _ v t D UL HJ2 HARU HARU2 HPOBJ HUL HDUL HLIVE2 HFOOT HNODE).
  assert (HP2 : FSH_Fn_reader.pobj tfibsegs B ly2 S2 W2 mem2 v)
    by exact (pjw_pobj_journal STK_pj_write (spZ regs) FS_PSTAT_FP ly S U W mem md [] ly2 S2 U2 W2 mem2 md2 k2
                v D UL HJ2 HARU HARU2 HPOBJ HUL HDUL HLIVE2 HFOOT HH2 pjw_c_pstat_low).
  assert (HUL2 : ublocks_ok B tfibsegs ly2 S2 W2 mem2 UL).
  { apply (pjw_ublocks_journal STK_pj_write (spZ regs) FS_PSTAT_FP ly S U W mem md [] ly2 S2 U2 W2 mem2 md2 k2 UL
      HJ2 HARU HARU2 HUL).
    - intros a kk Hak. destruct (HUL a kk Hak) as (Hin & _).
      exact (pjw_c_bswap0_keep ly S W _ md _ bufF capF HAR HBS _ Hin).
    - exact (pjw_c_ul_not_pstat ly S W _ md mem UL HAR HUL). }
  eapply SRr_mono.
  { apply (pjw_epi_success W ly S U regs mem md ly2 S2 U2 W2 regs2 mem2 md2 k2 bufF _ capF
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 bufF /\
         pjw_succ B tfibsegs ly' S' W' mem' bufF t (negb (pretty =? 0)) (WriterApp.w_cap st') /\
         (exists C1 C2, ablocks B ly' S' = C1 ++ (bufF - HEAD, WriterApp.w_cap st' + HEAD) :: C2 /\
            C1 ++ C2 = ablocks B ly S) /\
         PjStruct.pj_node tfibsegs (mrestrict (w_H W') mem') (fun a k => In (a, k) UL) v t D /\
         (exists peak', peak <= peak' <= Z.max peak (live + 2 * WriterApp.w_cap st') /\
            fs_glob tfibsegs W' mem' (live + WriterApp.w_cap st') peak' (WriterApp.w_cnt st') (WriterApp.w_fail st')))
      HJ2 HARU2 HS Hsp2 Hcs Hra).
    intros regsF memF mdF H10 SBF.
    pose proof (pjw_avb_of_same_below W2 mem2 memF SBF) as AV.
    rewrite <- Ec.
    split; [exact H10|]. split; [|split; [|split]].
    + unfold pjw_succ. split; [unfold HEAD in Hb1; lia|]. split; [exact Hb1|].
      split; [exact Hpow|]. split; [exact Hlt|].
      split; [exact (pjw_rblock_avb ly2 S2 W2 mem2 memF _ md2 bufF capF (proj1 HARU2) AV Hrb)|].
      apply (pjw_p_zbytes_avb W2 mem2 memF bufF _ AV);
        [unfold HEAD in *; lia | rewrite length_app; cbn [length]; lia | exact Hz].
    + exact EBS.
    + exact (pjw_pj_node_avb ly2 S2 W2 mem2 memF _ md2 _ v t D UL (proj1 HARU2) AV HP2 HUL2 HDUL HN2).
    + exists peakF. split; [exact HPEAK|]. exact (pjw_fs_glob_avb W2 mem2 memF _ _ _ _ AV HGL). }
  intros W' c' _ HPOST. left. exists bufF. split; [rewrite <- Ef; exact Hf0|].
  rewrite <- EU2. exact (pjw_c_fpostU_k _ _ _ _ _ _ _ _ _ _ k2 _ _ _ _ _ HPOST Hk2).
- (* ---- failed = 1: NULL is returned, a buffer taken is freed ---- *)
  rewrite Hf1 in HS.
  assert (Hev2 : st_nev S2 + 1 <= EV_MAX).
  { pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev & _). unfold EV_fuzz_free in HEV. lia. }
  destruct (Z.eq_dec bufF 0) as [Hb0|Hb0].
  + (* nothing was taken *)
    assert (Hc0 : capF = 0).
    { destruct Hdisj as [(Hc0 & _)|(_ & Hrb & _)]; [exact Hc0|]. exfalso.
      destruct (fsw_rblock_low B ly2 S2 W2 _ md2 mem2 bufF capF (proj1 HARU2) Hrb) as (Hb1 & _).
      unfold HEAD in Hb1. lia. }
    assert (EU2 : U2 = U).
    { destruct HUS as [(EU & _)|[(V1 & V2 & EV & _)|(_ & EU)]];
        [exact EU | exfalso; exact (HnegU V1 V2 EV) | exfalso].
      destruct (HH2 (bufF - HEAD, HEAD) ltac:(rewrite EU; apply in_or_app; right; left; reflexivity))
        as (_ & m0 & Hm0 & _).
      destruct (fsw_ablock_low B ly2 S2 W2 _ md2 _ _ (proj1 HARU2) Hm0) as (H4 & _).
      cbn [fst] in H4. unfold HEAD in H4. lia. }
    assert (EA2 : ablocks B ly2 S2 = ablocks B ly S).
    { destruct HBS as [(_ & _ & EA)|[(_ & C1 & C2 & EA & _)|(X1 & X2 & _ & _ & EX & _)]];
        [exact EA | exfalso | exfalso; exact (HnegA X1 X2 EX)].
      assert (Hin : In (bufF - HEAD, capF + HEAD) (ablocks B ly2 S2))
        by (rewrite EA; apply in_or_app; right; left; reflexivity).
      destruct (fsw_ablock_low B ly2 S2 W2 _ md2 _ _ (proj1 HARU2) Hin) as (H4 & _). unfold HEAD in H4. lia. }
    subst U2.
    eapply SRr_mono.
    { apply (pjw_epi_failed_null W ly S U regs mem md ly2 S2 U W2 regs2 mem2 md2 k2 bufF _ capF
        (live + capF) peakF (WriterApp.w_cnt st') (WriterApp.w_fail st')
        (fun ly' S' W' regs' mem' md' =>
           getr regs' 10 = w64 0 /\
           Permutation (ablocks B ly' S') (ablocks B ly S) /\
           PjStruct.pj_node tfibsegs (mrestrict (w_H W') mem') (fun a k => In (a, k) UL) v t D /\
           (exists peak', peak <= peak' <= Z.max peak (live + 2 * WriterApp.w_cap st') /\
              fs_glob tfibsegs W' mem' live peak' (WriterApp.w_cnt st') (WriterApp.w_fail st')))
        HJ2 HARU2 HS Hsp2 Hcs Hra Hgp Htp Hs0 HFF HGL HH2 HRO2 Hb0).
      intros ly3 S3 W3 regsF memF mdF H10 HJ3 HARU3 EA3 HH3 HGL3.
      split; [exact H10|]. split; [|split].
      - rewrite EA3, EA2. apply Permutation_refl.
      - apply (pjw_pj_node_journal STK_pj_write (spZ regs) FS_PSTAT_FP ly S U W mem md [] ly3 S3 U W3 memF mdF
          (k2 + 0) _ v t D UL HJ3 HARU HARU3 HPOBJ HUL HDUL); [|exact HFOOT|exact HNODE].
        intros b n x Hb _ _. rewrite EA3, EA2. exact Hb.
      - exists peakF. split; [rewrite <- Ec; exact HPEAK|]. rewrite Hc0, Z.add_0_r in HGL3. exact HGL3. }
    intros W' c' _ HPOST. right. split; [rewrite <- Ef, Hf1; discriminate|].
    refine (pjw_c_fpostU_k _ _ _ _ _ _ _ _ _ _ (k2 + 0) _ _ _ _ _ HPOST _). unfold EV_fuzz_free. lia.
  + (* the buffer is freed *)
    destruct Hdisj as [(_ & Hb00 & _)|(Hpow & Hrb & Hlt & Hz)]; [exfalso; exact (Hb0 Hb00)|].
    assert (EU2 : U2 = U ++ [(bufF - HEAD, HEAD)]).
    { destruct HUS as [(_ & Eb)|[(V1 & V2 & EV & _)|(_ & EU)]];
        [exfalso; exact (Hb0 Eb) | exfalso; exact (HnegU V1 V2 EV) | exact EU]. }
    assert (EBS : exists C1 C2, ablocks B ly2 S2 = C1 ++ (bufF - HEAD, capF + HEAD) :: C2 /\
                                C1 ++ C2 = ablocks B ly S).
    { destruct HBS as [(Eb & _ & _)|[(_ & C1 & C2 & EA & EC)|(X1 & X2 & _ & _ & EX & _)]].
      - exfalso. exact (Hb0 Eb).
      - exists C1, C2. split; [exact EA | exact EC].
      - exfalso. exact (HnegA X1 X2 EX). }
    destruct EBS as (C1 & C2 & EA2 & EC).
    assert (Hnot : ~ In (bufF - HEAD, capF + HEAD) (ablocks B ly S)).
    { rewrite <- EC. exact (pjw_c_blk_once ly2 S2 W2 _ md2 C1 C2 _ _ (proj1 HARU2) EA2). }
    eapply SRr_mono.
    { apply (pjw_epi_failed_block W ly S U regs mem md ly2 S2 U2 W2 regs2 mem2 md2 k2 bufF _ capF
        (live + capF) peakF (WriterApp.w_cnt st') (WriterApp.w_fail st') capF U []
        (fun ly' S' W' regs' mem' md' =>
           getr regs' 10 = w64 0 /\
           Permutation (ablocks B ly' S') (ablocks B ly S) /\
           PjStruct.pj_node tfibsegs (mrestrict (w_H W') mem') (fun a k => In (a, k) UL) v t D /\
           (exists peak', peak <= peak' <= Z.max peak (live + 2 * WriterApp.w_cap st') /\
              fs_glob tfibsegs W' mem' live peak' (WriterApp.w_cnt st') (WriterApp.w_fail st')))
        HJ2 HARU2 HS Hsp2 Hcs Hra Hgp Htp Hs0 HFF HGL HH2 Hev2 HRO2 Hb0 EU2 Hrb ltac:(lia) Hnot).
      intros ly3 S3 W3 regsF memF mdF H10 HJ3 HARU3 (l1 & l2 & E2 & E3) HH3 HGL3.
      rewrite app_nil_r in HJ3, HARU3.
      assert (Hkeep : forall b, In b (ablocks B ly S) -> In b (ablocks B ly3 S3)).
      { intros b Hb.
        assert (Hb2 : In b (ablocks B ly2 S2)).
        { rewrite EA2. rewrite <- EC in Hb.
          apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; right; exact Hb]. }
        rewrite E2 in Hb2. rewrite E3. apply in_app_or in Hb2 as [Hb2|[Hb2|Hb2]]; apply in_or_app.
        - left. exact Hb2.
        - exfalso. apply Hnot. rewrite Hb2. exact Hb.
        - right. exact Hb2. }
      split; [exact H10|]. split; [|split].
      - rewrite E3, <- EC. apply (Permutation_app_inv _ _ _ _ (bufF - HEAD, capF + HEAD)).
        rewrite <- E2, <- EA2. apply Permutation_refl.
      - apply (pjw_pj_node_journal STK_pj_write (spZ regs) FS_PSTAT_FP ly S U W mem md [] ly3 S3 U W3 memF mdF
          (k2 + 1) _ v t D UL HJ3 HARU HARU3 HPOBJ HUL HDUL); [|exact HFOOT|exact HNODE].
        intros b n x Hb _ _. exact (Hkeep _ Hb).
      - exists peakF. split; [rewrite <- Ec; exact HPEAK|]. rewrite Z.add_simpl_r in HGL3. exact HGL3. }
    intros W' c' _ HPOST. right. split; [rewrite <- Ef, Hf1; discriminate|].
    rewrite app_nil_r in HPOST.
    refine (pjw_c_fpostU_k _ _ _ _ _ _ _ _ _ _ (k2 + 1) _ _ _ _ _ HPOST _). unfold EV_fuzz_free. lia.
Qed.

(* put's state for the final newline: write_value's fields, the request trace reset *)
#[local] Abbreviation pjw_st2 st1 := (WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed st1) (WriterApp.w_text st1)
  (WriterApp.w_cap st1) (WriterApp.w_cnt st1) (WriterApp.w_fail st1) []) [10]).

(* ================= after write_value: the branch on pretty, the newline put, the epilogue =================
   From the resume state at PJW_WV_RET (pjw_wv_call's continuation): pretty = 0 goes straight to PJW_PUT_RET
   (pjw_pretty0_to_epi), pretty <> 0 puts the newline (pjw_put_call), and both end in pjw_close_tail. Here the
   composite head / block shapes, the budgets of the put call and the count wev0 st' = wevk 0 st1 + wevk cap1 st2
   (pjw_c_wev_split) are assembled. *)
Lemma pjw_close_mid : forall (W : world tfibsegs) ly S U regs mem md ch v pretty (t : PjTree.jv) D UL live peak
    cnt fail regs3 ly2 S2 (W2 : world tfibsegs) U2 regsE memE mdE buf1,
  put_spec B tfibsegs -> fuzz_free_spec tfibsegs B -> fs_img_facts tfibsegs B ->
  afn_preU tfibsegs B STK_pj_write ly S U W regs mem md ch ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  fs_heads B ly S U -> Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE -> 0 <= pretty < alloc_ceiling ->
  PjStruct.pj_node tfibsegs (mrestrict (w_H W) mem) (fun a k => In (a, k) UL) v t D ->
  FSH_Fn_reader.pobj tfibsegs B ly S W mem v -> ublocks_ok B tfibsegs ly S W mem UL ->
  (forall a k, In (a, k) D -> In (a, k) UL) ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  Z.of_nat (length (WriterValue.wdoc t (negb (pretty =? 0)))) + 1 <= WMAX ->
  (let st' := WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0))) in
   st_nev S + wev0 st' + EV_fuzz_free <= EV_MAX /\ blocks_bytes S + 2 * (WriterApp.w_cap st' + HEAD) <= LIVE_MAX /\
   live + 2 * WriterApp.w_cap st' < 2 ^ 64 /\ cnt + wcalls st' < 2 ^ 64) ->
  getr regs3 8 = w64 pretty -> getr regs3 3 = w64 (as_gp B) -> getr regs3 4 = w64 (as_tp B) ->
  (forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 2 -> bv_unsigned q <> 8 ->
     bv_unsigned q <> 9 -> getr regs3 q = getr regs q) ->
  ajournal tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 memE) mdE (0 + wevk 0 (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) ->
  ARU tfibsegs B ly2 S2 U2 W2 memE mdE ->
  st_ok tfibsegs (Ereg regsE (pjw_extra regs buf1
      (Z.of_nat (length (WriterApp.w_text (pjw_st_wv t (negb (pretty =? 0)) cnt fail)))) (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail))))
    (fss_ret PJW_WV_RET 64 (pjw_cs_obj (WriterApp.w_failed (pjw_st_wv t (negb (pretty =? 0)) cnt fail))))
    (restrict (w_H W2) (YK11.mkst regsE (Z_to_bv 64 PJW_WV_RET) memE (YK11.seg_rom tfibsegs))) ->
  spZ regsE = spZ regs - FRAME_pj_write ->
  (forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regsE q = getr regs3 q) ->
  uswap U U2 0 buf1 0 ->
  wout_ok B tfibsegs ly2 S2 W2 memE (spZ regs - 56) buf1 (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_failed (pjw_st_wv t (negb (pretty =? 0)) cnt fail))
    (WriterApp.w_text (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) ->
  wbudget_kept S S2 0 0 cnt (WriterApp.w_failed (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_cnt (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) ->
  bswap (ablocks B ly S) (ablocks B ly2 S2) 0 buf1 0 (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) ->
  (exists peak', peak <= peak' <= Z.max peak (live - 0 + WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) /\
     fs_glob tfibsegs W2 memE (live + WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail) - 0) peak' (WriterApp.w_cnt (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_fail (pjw_st_wv t (negb (pretty =? 0)) cnt fail))) ->
  SRr tfibsegs W2 (cfg_at tfibsegs PJW_WV_RET regsE memE mdE)
    (fun W' c' =>
       let st' := WriterApp.putN (WriterApp.w0 cnt fail)
                    (WriterValue.wdpieces t (negb (pretty =? 0))) in
       (exists q, WriterApp.w_failed st' = 0 /\
        fpostU tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP regs ly S U W mem md (wev0 st')
          (U ++ [(q - HEAD, HEAD)])
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 q /\
             pjw_succ B tfibsegs ly' S' W' mem' q t (negb (pretty =? 0)) (WriterApp.w_cap st') /\
             (exists C1 C2, ablocks B ly' S' = C1 ++ (q - HEAD, WriterApp.w_cap st' + HEAD) :: C2 /\
                C1 ++ C2 = ablocks B ly S) /\
             PjStruct.pj_node tfibsegs (mrestrict (w_H W') mem') (fun a k => In (a, k) UL) v t D /\
             (exists peak', peak <= peak' <= Z.max peak (live + 2 * WriterApp.w_cap st') /\
                fs_glob tfibsegs W' mem' (live + WriterApp.w_cap st') peak'
                  (WriterApp.w_cnt st') (WriterApp.w_fail st'))) W' c')
       \/
       (WriterApp.w_failed st' <> 0 /\
        fpostU tfibsegs B STK_pj_write (spZ regs) FS_PSTAT_FP regs ly S U W mem md (wev0 st' + EV_fuzz_free) U
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 0 /\
             Permutation (ablocks B ly' S') (ablocks B ly S) /\
             PjStruct.pj_node tfibsegs (mrestrict (w_H W') mem') (fun a k => In (a, k) UL) v t D /\
             (exists peak', peak <= peak' <= Z.max peak (live + 2 * WriterApp.w_cap st') /\
                fs_glob tfibsegs W' mem' live peak' (WriterApp.w_cnt st') (WriterApp.w_fail st'))) W' c')).
Proof.
intros W ly S U regs mem md ch v pretty t D UL live peak cnt fail regs3 ly2 S2 W2 U2 regsE memE mdE buf1
  HPUT HFF HIMG HAPU HRO HHEADS HFRL Hpr HNODE HPOBJ HUL HDUL HGLOB HWMAX HBUD H83 H33 H43 HCS3
  HJW HARUW HSW HspW HCSW HUSW HOUTW HKEPTW HBSWW HGLW.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (K1 & K2 & K3 & K4 & K5).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HAPU) as HARU.
pose proof HAPU as ((HAR & Hra & Hra4 & Hgp & Htp & _) & HOK & _).
pose proof HBUD as (HEV & HLV & HL64 & HCN). pose proof HEV as HEV0.
pose proof HGLOB as (_ & _ & _ & _ & Hlive & _ & Hcnt & _).
pose proof (pjw_c_inv_wv t (negb (pretty =? 0)) cnt fail) as HI1.
pose proof (pjw_c_st_rel t (negb (pretty =? 0)) cnt fail) as (Rw & Rc & Rk).
pose proof HOUTW as (_ & _ & _ & _ & Hbufr & Hcapr & _ & _ & _ & _ & Hf01 & _ & Hdisj).
assert (Hc0buf : WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail) = 0 -> buf1 = 0).
{ intros E0. destruct Hdisj as [(_ & Hb & _)|(_ & (_ & _ & Hn & _) & _)]; [exact Hb | lia]. }
assert (Hinbuf : WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail) <> 0 ->
    In (buf1 - HEAD, WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail) + HEAD) (ablocks B ly2 S2)).
{ intros E0. destruct Hdisj as [(Hc & _)|(_ & (Hin & _) & _)]; [exact (False_ind _ (E0 Hc)) | exact Hin]. }
(* the buffer's head is in U2 once write_value took one (its uswap): put's head premise at the newline put *)
assert (HUin : WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail) <> 0 -> In (buf1 - HEAD, HEAD) U2).
{ intros E0. destruct HUSW as [(_ & Eb)|[(V1 & V2 & _ & EU)|(_ & EU)]].
  - exfalso. pose proof (Hinbuf E0) as Hin. rewrite Eb in Hin.
    destruct (fsw_ablock_low B ly2 S2 W2 _ mdE _ _ (proj1 HARUW) Hin) as (H4 & _). unfold HEAD in H4. lia.
  - rewrite EU. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
  - rewrite EU. apply in_or_app. right. left. reflexivity. }
assert (HH2 : fs_heads B ly2 S2 U2)
  by exact (pjw_c_heads0 ly S U W _ md ly2 S2 U2 W2 _ mdE buf1 _ HAR HHEADS (proj1 HARUW) (proj1 (proj2 HARUW))
              HUSW HBSWW Hc0buf Hinbuf (proj1 Hcapr)).
pose proof HJW as (_ & _ & _ & _ & _ & Hfrs & Hnev & _). cbn [app] in Hfrs.
assert (HCSE : forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 2 -> bv_unsigned q <> 8 ->
    bv_unsigned q <> 9 -> getr regsE q = getr regs q)
  by (intros q Hq H2 H8 H9; rewrite (HCSW q Hq); exact (HCS3 q Hq H2 H8 H9)).
assert (H8E : getr regsE 8 = w64 pretty) by (rewrite (HCSW 8%bv ltac:(unfold acallee_saved; pjw_f_bvz; lia)); exact H83).
destruct HGLW as (peak1 & Hpk1 & HGL1).
destruct (Z.eq_dec pretty 0) as [Hp0|Hp0].
- (* ---- pretty = 0: straight to the epilogue; pj_write's trace is write_value's ---- *)
  assert (Ep : negb (pretty =? 0) = false) by (rewrite Hp0; reflexivity).
  apply (pjw_pretty0_to_epi W ly S U regs mem md ly2 S2 U2 W2 regsE memE mdE (0 + wevk 0 (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) buf1 _
    (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_failed (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) _ HJW HARUW HSW HspW ltac:(rewrite H8E, Hp0; reflexivity) Hf01).
  intros regsF memF mdF HJF HARUF HSF HspF HCSF SBF.
  pose proof (pjw_avb_of_same_below W2 memE memF SBF) as AV.
  apply (pjw_close_tail W ly S U regs mem md ch v pretty t D UL live peak cnt fail ly2 S2 U2 W2 regsF memF mdF
    (0 + wevk 0 (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) buf1 (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_failed (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_text (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) peak1
    HAPU HHEADS HNODE HPOBJ HUL HDUL (proj1 Hlive) HFF HJF).
  + rewrite (pjw_c_doc_false t _ cnt fail Ep). unfold wevk. cbn [Z.eqb]. lia.
  + exact HEV.
  + exact HARUF.
  + exact HSF.
  + unfold FRAME_pj_write in HspF. exact HspF.
  + intros q Hq H2 H8 H9. rewrite (HCSF q Hq). exact (HCSE q Hq H2 H8 H9).
  + rewrite (HCSF 8%bv ltac:(unfold acallee_saved; pjw_f_bvz; lia)). exact H8E.
  + exact Hpr.
  + exact (pjw_c_obj_data_avb ly2 S2 W2 _ mdE memE memF _ _ _ _ (proj1 HARUW) AV
             (pjw_c_obj_data_of_wout ly2 S2 W2 memE _ _ _ _ _ HOUTW)).
  + rewrite (pjw_c_doc_false t _ cnt fail Ep). reflexivity.
  + rewrite (pjw_c_doc_false t _ cnt fail Ep). reflexivity.
  + intros Hf. destruct (pjw_putN_text _ _ Hf) as [_ Ht]. unfold pjw_st_wv. rewrite Ht.
    rewrite pjw_wdoc_split, Ep. cbn [WriterApp.w_text app]. rewrite app_nil_r. reflexivity.
  + rewrite (pjw_c_doc_false t _ cnt fail Ep). rewrite Z.sub_0_r in HGL1.
    exact (pjw_fs_glob_avb W2 memE memF _ _ _ _ AV HGL1).
  + lia.
  + exact HH2.
  + exact (pjw_c_arodata_at ly S U W regs mem md ly2 S2 U2 W2 memF mdF _ HJF HARU HARUF HRO).
  + exact HUSW.
  + exact HBSWW.
- (* ---- pretty <> 0: the newline put, then the epilogue ---- *)
  assert (Ep : negb (pretty =? 0) = true) by (apply negb_true_iff; apply Z.eqb_neq; exact Hp0).
  pose proof (pjw_c_doc_true t _ cnt fail Ep) as Hdoc.
  pose proof (pjw_c_wev_split (pjw_st_wv t (negb (pretty =? 0)) cnt fail) [10] HI1) as Hsplit.
  pose proof (pjw_c_wcalls_split (pjw_st_wv t (negb (pretty =? 0)) cnt fail) [10]) as Hcsplit.
  pose proof (pjw_put1_fields (pjw_st_wv t (negb (pretty =? 0)) cnt fail) [10]) as (Ff & Ft & Fc & Fn & Fl).
  pose proof (pjw_c_put1_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail) [10] (proj1 HI1)) as Hcapmono.
  pose proof (pjw_c_wevk_nonneg (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.put1 (pjw_rst (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) [10])) as Hnn.
  assert (Hk1 : 0 <= wcalls (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) by (unfold wcalls; lia).
  assert (Hk2 : 0 <= wcalls (WriterApp.put1 (pjw_rst (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) [10])) by (unfold wcalls; lia).
  rewrite Hdoc in HEV, HLV, HL64, HCN.
  rewrite Hsplit in HEV. rewrite Hcsplit in HCN. unfold EV_fuzz_free in HEV.
  pose proof (pjw_c_cnt_wv t (negb (pretty =? 0)) cnt fail (proj1 Hcnt) ltac:(lia)) as Ecnt1.
  pose proof (pjw_c_putN_text_len (WriterValue.wvpieces t (negb (pretty =? 0)) 0) (WriterApp.mkW 0 [] 0 cnt fail []))
    as Htl. cbn [WriterApp.w_text length] in Htl.
  change (WriterApp.putN (WriterApp.mkW 0 [] 0 cnt fail []) (WriterValue.wvpieces t (negb (pretty =? 0)) 0))
    with (pjw_st_wv t (negb (pretty =? 0)) cnt fail) in Htl.
  pose proof (proj1 HI1) as Hcap1.
  pose proof (pjw_c_wdoc_len_true t _ Ep) as Hdl.
  pose proof HKEPTW as (HcapW & HbbW & _).
  assert (Hbsz0 : bsz 0 = 0) by reflexivity.
  unfold pjw_rst in *.
  apply (pjw_put_call W ly S U regs mem md ly2 S2 U2 W2 regsE memE mdE (0 + wevk 0 (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) pretty buf1
    (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_failed (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_text (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (live + WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail) - 0) peak1
    (WriterApp.w_cnt (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_fail (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) _ HPUT HJW HARUW HSW HspW).
  + rewrite (HCSW 3%bv ltac:(unfold acallee_saved; pjw_f_bvz; lia)). exact H33.
  + rewrite (HCSW 4%bv ltac:(unfold acallee_saved; pjw_f_bvz; lia)). exact H43.
  + exact H8E.
  + exact Hp0.
  + exact Hpr.
  + exact HOUTW.
  + exact HGL1.
  + exact HUin.
  + exact HH2.
  + exact (pjw_c_arodata_at ly S U W regs mem md ly2 S2 U2 W2 memE mdE _ HJW HARU HARUW HRO).
  + exact HIMG.
  + exact (pjw_c_fpsub_buf ly S W _ md ly2 S2 W2 _ mdE buf1 _ HAR (proj1 HARUW) HBSWW (proj1 Hcapr) Hinbuf).
  + rewrite Hfrs. lia.
  + exact HcapW.
  + lia.
  + lia.
  + unfold wbudget_pre, pjw_st_nl. rewrite Hbsz0 in HbbW. rewrite Fc. lia.
  + intros ly3 S3 W3 U3 regsP memP mdP buf2 HJP HARUP HSP HspP HCSP HUSP HOUTP HKEPTP HBSP HGLP.
    unfold pjw_st_nl in *.
    destruct HGLP as (peak2 & Hpk2 & HGL2).
    pose proof HOUTP as (_ & _ & _ & _ & _ & Hcapr2 & _ & _ & _ & _ & _ & _ & Hdisj2).
    assert (HUS3 : uswap U U3 0 buf2 0)
      by exact (pjw_c_uswap_comp U U2 U3 buf1 _ buf2 (pjw_c_noneg_U ly S U W _ md HAR HOK)
                  (pjw_c_noneg_U ly2 S2 U2 W2 _ mdE (proj1 HARUW) (proj1 (proj2 HARUW)))
                  (proj2 (proj1 (proj2 HARUW))) Hc0buf HUSW HUSP).
    assert (HBS3 : bswap (ablocks B ly S) (ablocks B ly3 S3) 0 buf2 0
                     (WriterApp.w_cap (WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_text (pjw_st_wv t (negb (pretty =? 0)) cnt fail))
                        (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_cnt (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_fail (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) []) [10])))
      by exact (pjw_c_bswap_comp ly S W _ md ly2 S2 W2 _ mdE (ablocks B ly3 S3) buf1 _ buf2 _ HAR (proj1 HARUW)
                  Hc0buf HBSWW HBSP).
    apply (pjw_close_tail W ly S U regs mem md ch v pretty t D UL live peak cnt fail ly3 S3 U3 W3 regsP memP mdP
      (0 + wevk 0 (pjw_st_wv t (negb (pretty =? 0)) cnt fail) + wevk (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (pjw_st2 (pjw_st_wv t (negb (pretty =? 0)) cnt fail))) buf2 (WriterApp.w_cap (pjw_st2 (pjw_st_wv t (negb (pretty =? 0)) cnt fail)))
      (WriterApp.w_failed (pjw_st2 (pjw_st_wv t (negb (pretty =? 0)) cnt fail))) (WriterApp.w_text (pjw_st2 (pjw_st_wv t (negb (pretty =? 0)) cnt fail))) peak2
      HAPU HHEADS HNODE HPOBJ HUL HDUL (proj1 Hlive) HFF HJP).
    * rewrite Hdoc, (pjw_c_wev_split (pjw_st_wv t (negb (pretty =? 0)) cnt fail) [10] HI1). unfold pjw_rst. lia.
    * exact HEV0.
    * exact HARUP.
    * exact HSP.
    * unfold FRAME_pj_write in HspP. exact HspP.
    * intros q Hq H2 H8 H9. rewrite (HCSP q Hq). exact (HCSE q Hq H2 H8 H9).
    * rewrite (HCSP 8%bv ltac:(unfold acallee_saved; pjw_f_bvz; lia)). exact H8E.
    * exact Hpr.
    * exact (pjw_c_obj_data_of_wout ly3 S3 W3 memP _ _ _ _ _ HOUTP).
    * rewrite Hdoc. exact Ff.
    * rewrite Hdoc. exact Fc.
    * intros Hf2.
      assert (Hf' : WriterApp.w_failed (WriterApp.putN (WriterApp.w0 cnt fail)
                      (WriterValue.wdpieces t (negb (pretty =? 0)))) = 0) by (rewrite Hdoc, <- Ff; exact Hf2).
      destruct (pjw_putN_text _ _ Hf') as [_ Ht']. rewrite Ft, <- Hdoc, Ht'. reflexivity.
    * rewrite Hdoc, <- Fn, <- Fl.
      replace (live + WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail) - 0 +
               WriterApp.w_cap (WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_text (pjw_st_wv t (negb (pretty =? 0)) cnt fail))
                 (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_cnt (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_fail (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) []) [10]) - WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail))
        with (live + WriterApp.w_cap (WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_text (pjw_st_wv t (negb (pretty =? 0)) cnt fail))
                 (WriterApp.w_cap (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_cnt (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) (WriterApp.w_fail (pjw_st_wv t (negb (pretty =? 0)) cnt fail)) []) [10])) in HGL2 by lia.
      exact HGL2.
    * lia.
    * apply (pjw_c_heads0 ly S U W _ md ly3 S3 U3 W3 _ mdP buf2 _ HAR HHEADS (proj1 HARUP) (proj1 (proj2 HARUP))
        HUS3 HBS3).
      -- intros E0. destruct Hdisj2 as [(_ & Hb & _)|(_ & (_ & _ & Hn & _) & _)]; [exact Hb | lia].
      -- intros E0. destruct Hdisj2 as [(Hc & _)|(_ & (Hin & _) & _)]; [exact (False_ind _ (E0 Hc)) | exact Hin].
      -- exact (proj1 Hcapr2).
    * exact (pjw_c_arodata_at ly S U W regs mem md ly3 S3 U3 W3 memP mdP _ HJP HARU HARUP HRO).
    * exact HUS3.
    * exact HBS3.
Qed.

(* ================= pj_write_spec: the closing theorem =================
   The walk end to end: stage 1 (entry .. the __asan_memset call), stage 2 (the memset), stage 3 (.. the write_value
   call), stage 5 (write_value at level 0 and its return, pjw_wv_call), then pjw_close_mid / pjw_close_tail. The
   data premises ride from the entry to the call on pjw_avb (pjw_avb_entry_to_call). Callees are premises:
   write_value at level 0, put, fuzz_free; and fs_img_facts (the image's read-only literal "\n"); the runtime
   __asan_memset is the Section's RT. *)
Theorem pjw_pj_write_spec :
  write_value_spec_at B tfibsegs 0 -> put_spec B tfibsegs -> fuzz_free_spec tfibsegs B ->
  fs_img_facts tfibsegs B ->
  pj_write_spec B tfibsegs.
Proof.
intros HWV HPUT HFF HIMG.
unfold pj_write_spec.
intros ly S U W regs mem md ch v pretty t D UL live peak cnt fail HPRE HHEADS HFRL R10 R11 Hpr HNODE HPOBJ HUL HDUL
  HGLOB HPLAIN HDEPTH HWMAX HBUD.
destruct HPRE as [HAPU HRO].
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (K1 & K2 & K3 & K4 & K5).
pose proof (fsw_sp B _ ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof HAPU as ((HAR & Hra & Hra4 & Hgp & Htp & _) & _ & _).
assert (HSTKv : 4160 <= STK_pj_write) by (vm_compute; discriminate).
apply (pjw_to_memset W ly S U regs mem md ch _ HAPU).
intros regs1 mem1 md1 HJ1 HARU1 SB1 Hsp1 R1_1 R3_1 R4_1 R8_1 R9_1 R10_1 R11_1 R12_1 V24 V16 V8 Rs1.
apply (pjw_memset_step W ly S U regs mem md regs1 mem1 md1 _ HJ1 HARU1 Hsp1 R1_1 (eq_trans R3_1 Hgp)
  (eq_trans R4_1 Htp) R10_1 R11_1 R12_1).
intros regs2 mem2 md2 HJ2 HARU2 HP12 Hzero FR2 Hpres2.
(* the three saved words lie above the memset's window and the runtime's own *)
assert (Vm : forall a n v0, spZ regs - 24 <= a -> a + Z.of_nat n <= spZ regs ->
    val_mem tfibsegs (mrestrict (w_H W) mem1) a n v0 -> val_mem tfibsegs (mrestrict (w_H W) mem2) a n v0).
{ intros a n v0 Ha Hn Hv.
  apply (AF0x.val_mem_ext (mrestrict (w_H W) mem1) (mrestrict (w_H W) mem2) a n v0); [|exact Hv].
  intros k Hk. apply (mbyte_of_aview tfibsegs). apply FR2; [lia | lia | unfold FRAME_pj_write, ESTACK; lia]. }
apply (pjw_to_write_value W ly S U regs mem md regs2 mem2 md2 _ HJ2 HARU2).
- unfold spZ. rewrite (fsw_pres regs1 regs2 2%bv HP12 ltac:(unfold acallee_saved; pjw_f_bvz; lia)). exact Hsp1.
- rewrite (fsw_pres regs1 regs2 3%bv HP12 ltac:(unfold acallee_saved; pjw_f_bvz; lia)). exact R3_1.
- rewrite (fsw_pres regs1 regs2 4%bv HP12 ltac:(unfold acallee_saved; pjw_f_bvz; lia)). exact R4_1.
- rewrite (fsw_pres regs1 regs2 8%bv HP12 ltac:(unfold acallee_saved; pjw_f_bvz; lia)). exact R8_1.
- rewrite (fsw_pres regs1 regs2 9%bv HP12 ltac:(unfold acallee_saved; pjw_f_bvz; lia)). exact R9_1.
- exact Hzero.
- apply Vm; [lia | change (Z.of_nat 8) with 8; lia | exact V24].
- apply Vm; [lia | change (Z.of_nat 8) with 8; lia | exact V16].
- apply Vm; [lia | change (Z.of_nat 8) with 8; lia | exact V8].
- intros regs3 mem3 md3 HJ3 HARU3 Hsp3 R1_3 R3_3 R4_3 R8_3 R9_3 R10_3 R11_3 R12_3 R13_3 Z0 Z1 Z2 Z3 V24' V16' V8'
    SB3 HP23.
  assert (AV : pjw_avb W mem mem3) by exact (pjw_avb_entry_to_call W regs mem mem1 mem2 mem3 ltac:(lia) SB1 FR2 SB3).
  assert (HCS3 : forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 2 -> bv_unsigned q <> 8 ->
      bv_unsigned q <> 9 -> getr regs3 q = getr regs q).
  { intros q Hq H2 H8 H9. rewrite (fsw_pres regs2 regs3 q HP23 Hq), (fsw_pres regs1 regs2 q HP12 Hq).
    pose proof Hq as Hq'. unfold acallee_saved in Hq'.
    destruct Hq' as [E|[E|[E|[E|[E|E]]]]]; [contradiction | | | contradiction | contradiction | exact (Rs1 q E)].
    - assert (Eq : q = 3%bv) by (apply bv_eq; rewrite E; reflexivity). subst q. exact R3_1.
    - assert (Eq : q = 4%bv) by (apply bv_eq; rewrite E; reflexivity). subst q. exact R4_1. }
  pose proof (pjw_c_st_rel t (negb (pretty =? 0)) cnt fail) as (Rw & Rc & Rk).
  pose proof HBUD as (HEV & HLV & HL64 & HCN).
  pose proof HGLOB as (_ & _ & _ & _ & Hlive & _ & Hcnt & _).
  apply (pjw_wv_call W ly S U regs mem md regs3 mem3 md3 v pretty t D UL live peak cnt fail _ HWV HJ3 HARU3
    (pjw_arodata_avb W mem mem3 AV HRO) Hsp3 R1_3 (eq_trans R3_3 Hgp) (eq_trans R4_3 Htp) (eq_trans R8_3 R11)
    R10_3 (eq_trans R11_3 R10) (eq_trans R12_3 R11) R13_3 Hpr Z0 Z1 Z2 Z3 V24' V16' V8' HHEADS HFRL
    (pjw_pj_node_avb ly S W mem mem3 _ md _ v t D UL HAR AV HPOBJ HUL HDUL HNODE)
    (pjw_pobj_avb ly S W mem mem3 _ md v HAR AV HPOBJ) (pjw_ublocks_avb ly S W mem mem3 _ md UL HAR AV HUL)
    HDUL HPLAIN HDEPTH (pjw_fs_glob_avb W mem mem3 live peak cnt fail AV HGLOB)).
  + pose proof (pjw_c_wdoc_len t (negb (pretty =? 0))). lia.
  + unfold wbudget_pre. assert (Hb0 : bsz 0 = 0) by reflexivity. rewrite Hb0. unfold EV_fuzz_free in HEV. lia.
  + intros ly2 S2 W2 U2 regsE memE mdE buf1 HJW HARUW HSW HspW HCSW HUSW HOUTW HKEPTW HBSWW HNODEW HGLW.
    exact (pjw_close_mid W ly S U regs mem md ch v pretty t D UL live peak cnt fail regs3 ly2 S2 W2 U2
      regsE memE mdE buf1 HPUT HFF HIMG HAPU HRO HHEADS HFRL Hpr HNODE HPOBJ HUL HDUL HGLOB HWMAX HBUD
      (eq_trans R8_3 R11) (eq_trans R3_3 Hgp) (eq_trans R4_3 Htp) HCS3 HJW HARUW HSW HspW HCSW HUSW HOUTW HKEPTW
      HBSWW HGLW).
Qed.

End W.
