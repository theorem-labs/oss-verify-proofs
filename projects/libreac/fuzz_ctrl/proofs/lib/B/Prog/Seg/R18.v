(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 537 of its 580 lines of code are new or changed and 968 lines of the source are left out. *)
(* Segment R18 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x819d0, 0x81a4c], 32
   instructions, cut Inv_B819d0 -> cut Inv_B81a50 (plan-asan-ubsan.md section 2, row R18; section 4, DECL =
   declaration_of 0x83114). rule 24: no function proved (a slot segment).

   0x819d0 beqz a0 is taken (reac_ports_parse returned 0, the entry cut), so the sink jump 0x819d4 is not reached.
   0x819d8 ld a0,32(s1) reloads [A + 32] = 0 (RBE) and 0x819dc beqz a0 is taken, so the branch to the trap routine
   0x819e0 `j 82fa0` is not taken (plan T07). The two count checks: 0x819e4 ld a3,24(s1) = mrow + 16, the shadow
   byte of a3 (0x819e8 srli / 0x819ec add s10 / 0x819f0 lb) is 0 (the catalogue row is a registered global, so its
   aligned granule is addressable), so 0x819fc bnez is not taken; 0x819f4 ld a0,120(s1) = fr + 2528, 0x819f8
   lw a0,0(a0) = 4 n_in (the port word reac_ports_parse wrote), 0x81a00 lw a1,0(a3) = the row word at + 16, which is
   4 n_in too (RtmB.rb_row_ic), so 0x81a04 beq is taken and the sink jump 0x81a08 is not reached; the same for
   [A + 16] = mrow + 20 and fr + 2532 (0x81a0c .. 0x81a2c, sink 0x81a30 not reached). 0x81a34 .. 0x81a40
   sb zero,320..323(s3) clear the four shadow bytes of the declaration slot [fr + 2560, fr + 2592). 0x81a44
   ld a0,272(s1) = mrow, 0x81a48 ld a1,96(s1) = decl_slot fr and 0x81a4c jal declaration_of, returning to 0x81a50.

   declaration_of is taken on its lib/B contract (lib/B/Prog/declaration_of_c.v), a Section Hypothesis, never on
   its code: with a declared row (RtmB.rb_rtm_declok) it returns 1 and writes the row's declaration at decl_slot fr;
   it writes only those 32 bytes and its own stack window [sp - 2256, sp). Its contract asks for mem_inv, so the
   call runs on the normalized memory (MemNorm.evt_normalize) and is carried back.

   FRA / ENT move across the four shadow stores by RHelp.rh_sh_move, then across the callee's write set by
   Tac_slot.sl_fr_cl (AH from RHelp.rh_ah) and ent_store; RBE by RHelp.rh_RBE_keep_sh then rh_RBE_keep. Entry and
   exit are the official cuts Inv_B819d0_at / Inv_B81a50_at of lib/B/Prog/SlotInv.v. Both cuts carry s11 = 32,
   which the run and declaration_of keep.  v1.9.0 against the patched image: the pcs move +0x64, the spills are
   [A + 32] / [A + 24] / [A + 16] / [A + 272] / [A + 96] (patched [A + 48] / [A + 40] / [A + 32] / [A + 288] /
   [A + 104]), Phi_r + 18 is in s2 (patched s9), the 32 in s11 (patched s2), CUR's n - c in s9 (patched s8). *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcDecl RcLeaf RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import declaration_of_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot RHelp RtmB.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

(* A byte store `sb zero,k(s3)` into a cell run: the engine's store hook turns only a literal byte store into a
   one-byte cell; le1 v is [Z_to_bv 8 (bv_unsigned v)] by conversion (the hook of prover a Theorem Labs lane's lib/B/Prog/Seg/A4.v,
   here on the lib/Lib engine's fix_lit_store). *)
Local Ltac fix_lit_store ::=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) => change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

(* ---- small helpers ---- *)

Lemma r18_eqb_refl : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.

(* The shadow byte of an addressable granule reads as 0, so `bnez` on it is not taken. *)
Lemma r18_nz0 : negb (bv_eqb (sxb (Z_to_bv 8 0)) (Z_to_bv 64 0)) = false.
Proof.
  apply negb_false_iff. unfold sxb.
  replace (bv_signed (Z_to_bv 8 0)) with 0 by (vm_compute; reflexivity).
  unfold bv_eqb. reflexivity.
Qed.


(* The four zero shadow bytes S(fr) + 320 .. + 323 make the declaration slot [fr + 2560, fr + 2592) addressable. *)
Lemma r18_decl_addr : forall m fr, fr mod 8 = 0 -> 0 <= fr -> fr + 2592 <= APPMEM_END ->
  (forall a, fr + 2560 <= a < fr + 2592 -> app_mem a) ->
  bytes_at rsegs m (Sfr fr + 320) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  addressable m (fr + 2560) 32.
Proof.
  intros m fr H8 H0 Hend Happ (_ & _ & HB).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Happ; lia|]. exists (Z_to_bv 8 0).
  split; [|left; vm_compute; reflexivity].
  assert (Hd0 : 0 <= i / 8) by (apply Z.div_pos; lia).
  assert (E : shadow_addr (fr + 2560 + i) = Sfr fr + 320 + Z.of_nat (Z.to_nat (i / 8))).
  { rewrite Z2Nat.id by exact Hd0. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  rewrite E.
  assert (Hk : (Z.to_nat (i / 8) < 4)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by exact Hd0. Z.div_mod_to_equations. lia. }
  rewrite (HB _ Hk).
  assert (Hq : Z.to_nat (i / 8) = 0%nat \/ Z.to_nat (i / 8) = 1%nat \/ Z.to_nat (i / 8) = 2%nat \/
               Z.to_nat (i / 8) = 3%nat) by lia.
  destruct Hq as [Hq|[Hq|[Hq|Hq]]]; rewrite Hq; reflexivity.
Qed.

(* ---- the Lib-level run of [0x819d0, 0x81a50) ---- *)

(* What the two loads at 0x81a44 / 0x81a48 and the call at 0x81a4c need of the memory after the four stores. *)
Definition r18_pre (m1 : word -> option byte) (A spv lo mr D : Z) (row : list byte) : Prop :=
  ov_read_bytes rsegs m1 (wa (A + 272)) 8 = Some (le8 (Z_to_bv 64 mr)) /\
  ov_read_bytes rsegs m1 (wa (A + 96)) 8 = Some (le8 (Z_to_bv 64 D)) /\
  stk rsegs m1 lo spv /\
  bytes_at rsegs m1 mr row /\
  (exists ob, rw_cells rsegs m1 D [CB 32 ob]) /\
  asan_cells m1 /\ shadow_rw m1 /\ addressable m1 mr 296 /\ addressable m1 D 32.

Ltac r18_shfix :=
  repeat match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (MState.unsigned_lit x) by lia
  end.

Lemma r18_evt : declaration_of_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10v s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A D mr q v1 v2 lo : Z) (row junk : list byte),
    s1v = Z_to_bv 64 A -> s10v = Z_to_bv 64 ASAN_K -> a0v = Z_to_bv 64 0 ->
    0 <= A -> A + 448 <= 2 ^ 64 ->
    HIGHMEM_BEG <= lo -> lo + DECLARATION_OF_K <= bv_unsigned sp -> bv_unsigned sp <= APPMEM_END ->
    0 <= mr -> mr + 296 <= AC.GT -> mr mod 8 = 0 ->
    AC.GT <= bv_unsigned s3v -> bv_unsigned s3v + 324 <= HIGHMEM_BEG ->
    0 <= q -> q + 8 <= 2 ^ 64 ->
    AC.GT <= D -> D + 32 <= 2 ^ 64 ->
    (D + 32 <= bv_unsigned sp - DECLARATION_OF_K \/ bv_unsigned sp <= D) ->
    app_mem (D + 32) ->
    length row = 296%nat -> RcDecl.decl_ok row = true ->
    ov_read_bytes rsegs m (wa (A + 32)) 8 = Some (le8 (Z_to_bv 64 0)) ->
    ov_read_bytes rsegs m (wa (A + 24)) 8 = Some (le8 (Z_to_bv 64 (mr + 16))) ->
    ov_read_bytes rsegs m (wa (A + 16)) 8 = Some (le8 (Z_to_bv 64 (mr + 20))) ->
    ov_read_bytes rsegs m (wa (A + 120)) 8 = Some (le8 (Z_to_bv 64 q)) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 16) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 20) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa q) 4 = Some (le4 (Z_to_bv 64 v1)) ->
    ov_read_bytes rsegs m (wa (q + 4)) 4 = Some (le4 (Z_to_bv 64 v2)) ->
    ov_read_bytes rsegs m (wa (mr + 16)) 4 = Some (le4 (Z_to_bv 64 v1)) ->
    ov_read_bytes rsegs m (wa (mr + 20)) 4 = Some (le4 (Z_to_bv 64 v2)) ->
    rw_cells rsegs m (bv_unsigned s3v + 320) [CB 4 junk] ->
    MN.ro_agree rsegs m ->
    (forall m1, munch [(bv_unsigned s3v + 320, bv_unsigned s3v + 324)] m m1 -> wmono rsegs m m1 ->
       bytes_at rsegs m1 (bv_unsigned s3v + 320) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
       r18_pre m1 A (bv_unsigned sp) lo mr D row) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m1 m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x81a50) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1v /\
         getr R 18 = s2 /\ getr R 19 = s3v /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\
         getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10v /\ getr R 27 = s11 /\
         getr R 10 = Z_to_bv 64 1 /\
         munch [(bv_unsigned s3v + 320, bv_unsigned s3v + 324)] m m1 /\ wmono rsegs m m1 /\
         bytes_at rsegs m1 (bv_unsigned s3v + 320) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] /\
         munch [(bv_unsigned sp - DECLARATION_OF_K, bv_unsigned sp); (D, D + 32)] m1 m' /\ wmono rsegs m1 m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' D [CB 32 (RcDecl.decl row)])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10v s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x819d0) fc None m (seg_rom rsegs)).
Proof.
  intros DC ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10v s11 t3 t4 t5 t6
    Fr fc m A D mr q v1 v2 lo row junk -> -> -> HA0 HAb Hlo HlK Hsp Hmr0 Hmrb Hmr8 HSH0 HSHb Hq0 Hqb HD0 HDb
    Hdsp Hdapp Hrowlen Hdecl R32 R24 R16 R120 K16 K20 Q1 Q2 M16 M20 RWsh HRO HPRE.
  unfold AC.GT in *.
  assert (Hspv : 0 <= bv_unsigned sp < 2 ^ 64) by apply bv_unsigned_in_range.
  pose proof (rw_cells_bound _ _ _ _ RWsh) as HBsh. cbn [cells_size csize Nat.add] in HBsh.
  pose proof (munch_refl [(bv_unsigned s3v + 320, bv_unsigned s3v + 324)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 819d0 beqz a0 (taken) *)
  step. if_true.
  (* 819d8 ld a0,32(s1) ; 819dc beqz a0 (taken; the trap 819e0 is not reached) *)
  step. step. if_true.
  (* 819e4 ld a3,24(s1) ; 819e8 srli a0,a3,3 ; 819ec add a0,a0,s10 *)
  step. step. step. r18_shfix.
  (* 819f0 lb a1,0(a0) ; 819f4 ld a0,120(s1) ; 819f8 lw a0,0(a0) *)
  step. step. step.
  (* 819fc bnez a1 (not taken) *)
  step. first [ if_false | if_false_by r18_nz0 ].
  (* 81a00 lw a1,0(a3) ; 81a04 beq a0,a1 (taken) *)
  step. step. if_true_by (r18_eqb_refl (sx32 (Z_to_bv 64 v1))).
  (* 81a0c ld a3,16(s1) ; 81a10 srli ; 81a14 add *)
  step. step. step. r18_shfix.
  (* 81a18 lb a1,0(a0) ; 81a1c ld a0,120(s1) ; 81a20 lw a0,4(a0) *)
  step. step. step.
  (* 81a24 bnez a1 (not taken) *)
  step. first [ if_false | if_false_by r18_nz0 ].
  (* 81a28 lw a1,0(a3) ; 81a2c beq a0,a1 (taken) *)
  step. step. if_true_by (r18_eqb_refl (sx32 (Z_to_bv 64 v2))).
  (* 81a34 .. 81a40 : the four shadow stores, into the 4-byte cell run at S(fr) + 320 *)
  step. step. step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) => tryif constr_eq mm m1 then idtac else rename mm into m1
  end.
  assert (B4 : bytes_at rsegs m1 (bv_unsigned s3v + 320) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]).
  { lazymatch goal with
    | H : rw_cells rsegs m1 (bv_unsigned s3v + 320) ?cs |- _ =>
        destruct H as ((_ & HB) & _); eapply bytes_at_ext; [exact HB | first [reflexivity | vm_compute; reflexivity]]
    end. }
  assert (MI : MN.ro_agree rsegs m1).
  { apply (rh_ro_keep m m1 [(bv_unsigned s3v + 320, bv_unsigned s3v + 324)] HRO MU). intros x Hx.
    pose proof (rh_ro_lt x Hx) as Hlt. unfold AC.GT in Hlt. cbn [outside]. split; [lia | exact I]. }
  destruct (HPRE m1 MU WM B4)
    as (R272 & R96 & STc & HROW & (ob & HOB) & HAC & HSW & HAmr & HAD).
  (* 81a44 ld a0,272(s1) ; 81a48 ld a1,96(s1) ; 81a4c jal declaration_of *)
  step. step. step.
  pose proof (MN.mem_rel_normalize rsegs m1 MI) as REL.
  eapply evt_mono.
  { eapply MN.evt_normalize; [vm_compute; reflexivity | exact MI |].
    eapply DC with (lo := lo) (row := row) (ob := ob);
      rewrite ?(MState.unsigned_lit mr) by lia; rewrite ?(MState.unsigned_lit D) by lia.
    - apply rh_stk_norm; [exact MI | exact STc | apply rh_not_ro_hi; unfold AC.GT, HIGHMEM_BEG in *; lia].
    - lia.
    - exact Hmr8.
    - exact Hrowlen.
    - apply MN.bytes_at_normalize; [exact MI | exact HROW].
    - apply rh_rwc_norm; [exact MI | exact HOB | apply rh_not_ro_hi; cbn; unfold AC.GT; lia].
    - right; lia.
    - left; unfold HIGHMEM_BEG, DECLARATION_OF_K in *; lia.
    - exact Hdsp.
    - apply MN.mem_inv_normalize.
    - exact (rh_acells_rel m1 _ REL HAC).
    - exact (rh_shrw_rel m1 _ REL HSW).
    - exact Hlo.
    - exact Hsp.
    - exact (rh_addr_rel m1 _ _ _ REL HAmr).
    - exact (rh_addr_rel m1 _ _ _ REL HAD).
    - exact Hdapp.
    - right; unfold RT_HI; lia. }
  intros msx (msx0 & Pn & MR & RS).
  unfold declaration_of_post in Pn. rewrite Hdecl in Pn.
  destruct Pn as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MUc0 & WMc0 & _ & STq0 & HRW0 & _ & _ & _).
  subst msx0.
  destruct msx as [regs1 fregs1 pcv1 svc1 resv1 fcsr1 mem1 rom1].
  destruct MR as (Hr1 & Hf1 & Hpc1 & Hsvc1 & Hres1 & Hfc1 & Hrom1 & Hmem).
  cbn in Hr1, Hf1, Hpc1, Hsvc1, Hres1, Hfc1, Hrom1, Hmem, RS.
  rewrite ?(MState.unsigned_lit D) in MUc0, HRW0 by lia.
  exists regs1, m1, mem1.
  split.
  { unfold MS. subst. f_equal.
    first [ apply ret_pc_even; [lia | reflexivity] | symmetry; apply ret_pc_even; [lia | reflexivity] ]. }
  subst regs1.
  do 16 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM|]. split; [exact B4|].
  split; [exact (MN.munch_rel rsegs _ m1 _ mem1 m0' REL Hmem RS MUc0)|].
  split; [exact (MN.wmono_rel rsegs m1 _ mem1 m0' REL Hmem RS WMc0)|].
  split; [exact (rh_stk_back mem1 m0' _ _ Hmem STq0)|].
  exact (rh_rwc_back mem1 m0' D [CB 32 (RcDecl.decl row)] Hmem ltac:(unfold AC.GT; lia) ltac:(cbn; lia) HRW0).
Qed.

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* declaration_of (0x83114), taken on its lib/B contract. *)
Hypothesis DC : declaration_of_contract.

Lemma seg_R18 : forall b : nat,
  Hat B APIf ra (Inv_B81a50_at B APIf ra) b -> Hat B APIf ra (Inv_B819d0_at B APIf ra) b.
Proof.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hb6 & HHB & H22 & HOUR & HCUR & Hsp96 & HRBE & H21 & Hb0 & HRF & H18 & Ha0 & Hu1 & Hu2 &
     Hsp120 & Hsp24 & Hsp16 & H27)).
  subst c. subst b. rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_win B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (Hfrpl & HfrA & _ & Hfrwr).
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (HGTfr & Happfr).
  pose proof (rh_hb B APIf ra g fr phi (rnb g 0) regs mem md HFRA) as (Hphinz & Hphi4k & Hphistk & _ & Hphiapp).
  pose proof (rh_sh_in B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as Hshin.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (rnb g 0) ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HKd : DECLARATION_OF_K = 2256) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (W0 & W1 & _); split; [exact W0 | exact W1]).
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HA4 : A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  rewrite Haspz in Hwlo, Hwstk, Hfrpl.
  assert (Hspb : 0 <= sp <= APPMEM_END) by (unfold APPMEM_END in *; lia).
  assert (Hesp : bv_unsigned (getr regs 2) = sp)
    by (rewrite Hr2; apply MState.unsigned_lit; unfold APPMEM_END in *; lia).
  unfold AC.GT in HGTfr.
  assert (HspHM : HIGHMEM_BEG + 1040000 <= sp) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (HSfrhi : Sfr fr + 392 <= HIGHMEM_BEG).
  { pose proof (Hshin (Sfr fr + 391) ltac:(lia)) as (IS & _).
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in IS |- *. lia. }
  assert (HSfrGT : AC.GT <= Sfr fr) by (unfold Sfr, shadow_addr, ASAN_K, AC.GT; Z.div_mod_to_equations; lia).
  (* the turn's model facts *)
  pose proof HRF as (HRB0 & Hnz & H20 & HF).
  destruct (rb_rtn (g_in g) (Z.of_nat 0) Hnz) as (_ & Hnb & HLF).
  change (rt_n (g_in g) (Z.of_nat 0)) with (rnb g 0) in Hnb, HLF.
  change (Z.of_nat 0) with 0 in HF, HLF.
  pose proof (rb_mrow_range (g_in g)) as (Hmr0 & Hmr1 & Hmr8).
  pose proof (rb_mb_len (g_in g)) as Hmblen.
  pose proof (rb_rtm_declok (g_in g)) as Hdeclok.
  pose proof (rb_decl_len (g_in g)) as Hdlen.
  assert (Hsz : AC.a_size (rnb g 0) = rnb g 0) by (unfold AC.a_size; lia).
  destruct HHB as (Hnz0 & HAphi0). pose proof HAphi0 as HAphi. rewrite Hsz in HAphi.
  pose proof (rh_blk_fr B APIf ra g fr phi (rnb g 0) regs mem md HFRA ltac:(lia)) as Hblkfr.
  (* RBE's facts the run reads *)
  pose proof HRBE as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
    S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUTA & HA2176 & HNM & HOURa & HTBL & HBOX & HMROW &
    _).
  pose proof (rh_spill_at regs mem A 32 0 S32 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q32.
  pose proof (rh_spill_at regs mem A 24 (mrow (g_in g) + 16) S24 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q24.
  pose proof (rh_spill_at regs mem A 16 (mrow (g_in g) + 20) S16 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q16.
  pose proof (rh_spill_at regs mem A 120 (fr + 2528) S120 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q120.
  (* the catalogue row is addressable, so its granule at + 16 has shadow byte 0 *)
  assert (HAmr : forall mm, (forall a, CAT <= a < CAT + 3256 -> addressable mm a 1) ->
            addressable mm (mrow (g_in g)) 296).
  { intros mm Hc. apply rh_addr_join; [unfold CAT in *; lia | lia | unfold CAT, APPMEM_END in *; lia |].
    intros i Hi. apply Hc. lia. }
  pose proof (HAmr mem (rh_cat_addr B APIf ra g fr _ regs mem md HFRA)) as HAmr0.
  assert (HA16 : addressable mem (mrow (g_in g) + 16) 8)
    by (apply (addressable_sub mem (mrow (g_in g)) 296 16 8 HAmr0); lia).
  assert (Ksh16 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 16) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
    by (apply (rh_meta0 mem (mrow (g_in g) + 16)); [exact HA16 | Z.div_mod_to_equations; lia | lia]).
  assert (Ksh20 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 20) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
    by (apply (rh_meta0 mem (mrow (g_in g) + 16)); [exact HA16 | Z.div_mod_to_equations; lia | lia]).
  (* the four words the count checks compare *)
  assert (M16 : bytes_at rsegs mem (mrow (g_in g) + 16) (le4 (Z_to_bv 64 (4 * RcLeaf.n_in (rt_pbs (g_in g)))))).
  { rewrite <- (rb_row_ic (g_in g)).
    pose proof (rh_ba_sub mem _ _ 16 4 HMROW ltac:(lia)) as Hs.
    replace (mrow (g_in g) + Z.of_nat 16) with (mrow (g_in g) + 16) in Hs by lia. exact Hs. }
  assert (M20 : bytes_at rsegs mem (mrow (g_in g) + 20) (le4 (Z_to_bv 64 (4 * RcLeaf.n_out (rt_pbs (g_in g)))))).
  { rewrite <- (rb_row_oc (g_in g)).
    pose proof (rh_ba_sub mem _ _ 20 4 HMROW ltac:(lia)) as Hs.
    replace (mrow (g_in g) + Z.of_nat 20) with (mrow (g_in g) + 20) in Hs by lia. exact Hs. }
  unfold u32 in Hu1, Hu2.
  (* the four shadow bytes are present and writable: a 4-byte cell run *)
  assert (HRWsh : exists junk, rw_cells rsegs mem (Sfr fr + 320) [CB 4 junk]).
  { pose proof HRT as (_ & HSW0 & _).
    destruct (rh_bytes_of_present 4%nat mem (Sfr fr + 320) ltac:(unfold AC.GT in HSfrGT; lia)
                ltac:(unfold HIGHMEM_BEG in HSfrhi; lia)) as (junk & Hj & Hjl).
    { intros k Hk. destruct (Hshin (Sfr fr + 320 + Z.of_nat k) ltac:(lia)) as (Hsa & _).
      exact (proj2 (HSW0 _ Hsa)). }
    exists junk. rewrite <- Hjl. apply rh_rwc_CB; [exact Hj|]. rewrite Hjl.
    split; [unfold AC.GT in HSfrGT; lia|]. split; [unfold HIGHMEM_BEG in HSfrhi; cbn; lia|].
    intros i Hi. cbn in Hi. destruct (Hshin (Sfr fr + 320 + i) ltac:(lia)) as (Hsa & _).
    exact (proj1 (HSW0 _ Hsa)). }
  destruct HRWsh as (junk & HRWsh).
  assert (Hs3 : bv_unsigned (getr regs 19) = Sfr fr).
  { unfold rg in Hr19. rewrite Hr19. apply MState.unsigned_lit. unfold AC.GT, HIGHMEM_BEG in *. lia. }
  (* the run *)
  eapply (sl_run_lib regs (Z_to_bv 64 0x819d0) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81a50 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 27 = getr regs 27 /\ getr R 18 = getr regs 18 /\ getr R 10 = Z_to_bv 64 1 /\
       exists m1, munch [(Sfr fr + 320, Sfr fr + 324)] mem m1 /\ wmono rsegs mem m1 /\
         bytes_at rsegs m1 (Sfr fr + 320) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] /\
         munch [(sp - DECLARATION_OF_K, sp); (decl_slot fr, decl_slot fr + 32)] m1 mem' /\ wmono rsegs m1 mem' /\
         stk rsegs mem' (g_S g - AF.SLOT_STACK) sp /\
         rw_cells rsegs mem' (decl_slot fr) [CB 32 (RcDecl.decl (rt_mb (g_in g)))])
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    unfold rg, a0v in Ha0, Hr9, Hr26.
    eapply evt_mono.
    + apply (r18_evt DC) with (A := A) (D := decl_slot fr) (mr := mrow (g_in g))
        (q := fr + 2528) (v1 := 4 * RcLeaf.n_in (rt_pbs (g_in g))) (v2 := 4 * RcLeaf.n_out (rt_pbs (g_in g)))
        (lo := g_S g - AF.SLOT_STACK) (row := rt_mb (g_in g)) (junk := junk);
      repeat match goal with
      | |- context [bv_unsigned ?s] =>
          first [ progress change (bv_unsigned s) with (AC.aspZ regs)
                | progress change (bv_unsigned s) with (bv_unsigned (getr regs 19)); rewrite Hs3 ]
      end;
      rewrite ?Haspz;
      [ exact Hr9 | exact Hr26 | exact Ha0 | lia | exact HA4
      | lia | lia | lia | unfold CAT in *; lia | unfold CAT, AC.GT in *; lia | exact Hmr8
      | exact HSfrGT | lia | lia | lia | unfold decl_slot, AC.GT; lia | unfold decl_slot; lia
      | unfold decl_slot; destruct (Hfrpl DECLARATION_OF_K ltac:(lia)) as [Hc|Hc]; [left | right]; lia
      | unfold decl_slot; apply Happfr; lia
      | exact Hmblen | exact Hdeclok
      | exact (rh_rdn mem _ _ 8 Q32 ltac:(apply length_le8))
      | exact (rh_rdn mem _ _ 8 Q24 ltac:(apply length_le8))
      | exact (rh_rdn mem _ _ 8 Q16 ltac:(apply length_le8))
      | exact (rh_rdn mem _ _ 8 Q120 ltac:(apply length_le8))
      | exact Ksh16 | exact Ksh20
      | exact (rh_rdn mem _ _ 4 Hu1 ltac:(apply length_le4))
      | replace (fr + 2528 + 4) with (fr + 2532) by lia; exact (rh_rdn mem _ _ 4 Hu2 ltac:(apply length_le4))
      | exact (rh_rdn mem _ _ 4 M16 ltac:(apply length_le4))
      | exact (rh_rdn mem _ _ 4 M20 ltac:(apply length_le4))
      | exact HRWsh | exact Hro | ].
      intros m1 MU1 WM1 B4.
      (* FRA / ENT at m1 *)
      destruct (rh_sh_move B APIf ra empty FF g fr (hb1 phi (rnb g 0)) regs regs mem m1 md 320 324 HFRA HENT
                  ltac:(lia) ltac:(lia) ltac:(lia) MU1 WM1
                  ltac:(intros qq Hqq; exact (rh_ba_rd m1 (Sfr fr + 320) _ qq B4 ltac:(cbn; lia)))
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as (HFRA1 & _).
      pose proof HFRA1 as HF1.
      destruct HF1 as (A1 & sp1 & s51 & HRT1 & HAH1 & Hro1 & _ & _ & _ & Hr21 & _ & Haspz1 & _ & _ & _ & Hr91 &
        _ & _ & _ & _ & _ & _ & HAS1 & Hspa1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin1 & _).
      assert (Esp1 : sp1 = sp) by (rewrite Haspz in Haspz1; lia). subst sp1.
      assert (EA1 : A1 = A) by (exact (rh_rg9_eq regs A A1 Hr9 Hr91 HA64 ltac:(unfold APPMEM_END in *; lia))).
      subst A1.
      destruct HRT1 as (HAC1 & HSW1 & _).
      assert (HoutW1 : forall x, (x < Sfr fr + 320 \/ Sfr fr + 324 <= x) -> outside [(Sfr fr + 320, Sfr fr + 324)] x)
        by (intros x Hx; cbn [outside]; split; [lia | exact I]).
      assert (Q272 : q64 m1 (A + 272) (mrow (g_in g))).
      { unfold q64. apply (rh_keep _ mem m1 _ _ MU1); [|exact (rh_spill_at regs mem A 272 _ S272 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia))].
        rewrite length_le8. intros x Hx. apply HoutW1. right. unfold HIGHMEM_BEG in *. lia. }
      assert (Q96 : q64 m1 (A + 96) (decl_slot fr)).
      { unfold q64. apply (rh_keep _ mem m1 _ _ MU1); [|exact (rh_spill_at regs mem A 96 _ Hsp96 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia))].
        rewrite length_le8. intros x Hx. apply HoutW1. right. unfold HIGHMEM_BEG in *. lia. }
      split; [exact (rh_rdn m1 _ _ 8 Q272 ltac:(apply length_le8))|].
      split; [exact (rh_rdn m1 _ _ 8 Q96 ltac:(apply length_le8))|].
      split; [exact (proj1 (LFr.stk_split rsegs m1 (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin1 ltac:(lia)))|].
      split.
      { apply (rh_keep _ mem m1 _ _ MU1); [|exact HMROW].
        rewrite Hmblen. intros x Hx. apply HoutW1. left. unfold CAT, AC.GT in *. lia. }
      split.
      { pose proof (fra_frame B APIf ra g fr _ regs m1 md HFRA1) as (_ & _ & _ & Hfrwr1).
        destruct (rh_bytes_of_present 32%nat m1 (decl_slot fr) ltac:(unfold decl_slot; lia)
                    ltac:(unfold decl_slot, APPMEM_END in *; lia)) as (ob & Hob & Hobl).
        { intros k Hk. rewrite <- rh_mbyte_mrd.
          exact (rh_frame_rd B APIf ra g fr _ regs m1 md HFRA1 (decl_slot fr + Z.of_nat k)
                   ltac:(unfold decl_slot; lia)). }
        exists ob. rewrite <- Hobl. apply rh_rwc_CB; [exact Hob|]. rewrite Hobl.
        split; [unfold decl_slot; lia|]. split; [unfold decl_slot, APPMEM_END in *; lia|].
        intros i Hi. apply Hfrwr1. unfold decl_slot. cbn in Hi. lia. }
      split; [exact HAC1|]. split; [exact HSW1|].
      split; [exact (HAmr m1 (rh_cat_addr B APIf ra g fr _ regs m1 md HFRA1))|].
      unfold decl_slot. apply (r18_decl_addr m1 fr Hfr8 ltac:(lia) ltac:(unfold APPMEM_END in *; lia));
        [intros a Ha; apply Happfr; lia | exact B4].
    + intros ms' (R & m1 & m' & E & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 &
                  P26 & P27 & P10 & MU1 & WM1 & B4 & MU2 & WM2 & ST2 & HRW).
      exists R, (Z_to_bv 64 0x81a50), m'. split; [exact E|].
      split; [reflexivity|].
      split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P20|]. split; [exact P21|].
      split; [exact P22|]. split; [exact P23|]. split; [exact P24|]. split; [exact P25|].
      split; [exact P26|]. split; [exact P27|]. split; [exact P18|]. split; [exact P10|].
      match type of MU2 with
      | context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) in MU2, ST2
      end.
      rewrite Haspz in MU2, ST2.
      match type of MU1 with
      | context [bv_unsigned ?s] => change (bv_unsigned s) with (bv_unsigned (getr regs 19)) in MU1, B4
      end.
      rewrite Hs3 in MU1, B4.
      exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [exact B4|].
      split; [exact MU2|]. split; [exact WM2|]. split; [exact ST2 | exact HRW].
  - intros R pc' mem' regs' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K18 & K10 &
       m1 & MU1 & WM1 & B4 & MU & WM & ST' & HRW) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact K20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 1) by (rewrite Hreg; exact K10).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    (* step 1: the four shadow stores *)
    destruct (rh_sh_move B APIf ra empty FF g fr (hb1 phi (rnb g 0)) regs regs mem m1 md 320 324 HFRA HENT
                ltac:(lia) ltac:(lia) ltac:(lia) MU1 WM1
                ltac:(intros qq Hqq; exact (rh_ba_rd m1 (Sfr fr + 320) _ qq B4 ltac:(cbn; lia)))
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as (HFRA1 & HENT1).
    set (W1 := [(Sfr fr + 320, Sfr fr + 324)]).
    assert (HoutW1 : forall x, (x < Sfr fr + 320 \/ Sfr fr + 324 <= x) -> outside W1 x)
      by (intros x Hx; unfold W1; cbn [outside]; split; [lia | exact I]).
    assert (HappW1 : forall x, app_mem x -> outside W1 x).
    { intros x Hx. destruct (rh_out_dec W1 x) as [Ho|Ho]; [exact Ho|]. exfalso.
      unfold W1 in Ho. cbn [outside] in Ho. destruct (Hshin x ltac:(lia)) as (Hsx & _).
      exact (app_not_shadow x Hx Hsx). }
    assert (HRBE1 : RBE g fr regs m1).
    { apply (rh_RBE_keep_sh g fr regs regs W1 mem m1 A HRBE MU1 Hfr8 ltac:(unfold AC.GT; lia) Hr9 ltac:(lia)
               HA4 eq_refl).
      - intros x Hx. apply HoutW1. right. unfold HIGHMEM_BEG in *. lia.
      - intros x Hx. unfold W1 in Hx. cbn [outside] in Hx. lia. }
    assert (HRF1 : RFb g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs m1).
    { apply (rh_RFb_keep g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs regs W1 mem m1 MU1
               (rb_RID_len (g_in g) 0) (rb_RFG_len (g_in g) 0 ltac:(lia)) ltac:(lia) HLF);
        [ intros x Hx; apply HappW1, Happfr; lia
        | intros x Hx; apply HappW1, Hphiapp; lia
        | reflexivity | reflexivity | reflexivity | reflexivity | exact HRF ]. }
    assert (HHB1 : HB m1 phi (rnb g 0)).
    { split; [exact Hnz0|]. rewrite Hsz. apply (rh_addr_keep_rng mem m1 W1 phi (rnb g 0) HAphi MU1).
      intros i Hi. destruct (rh_out_dec W1 (shadow_addr (phi + i))) as [Ho|Ho]; [exact Ho|]. exfalso.
      unfold W1 in Ho. cbn [outside] in Ho.
      pose proof (rh_sh_inv fr (phi + i) 320 324 Hfr8 ltac:(lia) ltac:(lia) ltac:(lia)) as Hx.
      destruct Hblkfr; lia. }
    assert (HAD1 : addressable m1 (decl_slot fr) 32).
    { unfold decl_slot. apply (r18_decl_addr m1 fr Hfr8 ltac:(lia) ltac:(unfold APPMEM_END in *; lia));
        [intros a Ha; apply Happfr; lia | exact B4]. }
    assert (Hsp96_1 : spill regs m1 96 (decl_slot fr)).
    { exact (rh_spill_keep regs regs mem m1 W1 A 96 _ Hsp96 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia) eq_refl MU1
               (fun x Hx => HoutW1 x ltac:(unfold HIGHMEM_BEG in *; lia))). }
    (* step 2: the callee's write set W *)
    pose proof HFRA1 as HF1.
    destruct HF1 as (A1 & sp1 & s51 & HRT1 & HAH1 & Hro1 & _ & _ & _ & Hr21 & _ & Haspz1 & Hstklo1 & _ & _ & Hr91 &
      _ & _ & _ & _ & _ & _ & HAS1 & Hspa1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin1 & _).
    assert (Esp1 : sp1 = sp) by (rewrite Haspz in Haspz1; lia). subst sp1.
    assert (EA1 : A1 = A)
      by (exact (rh_rg9_eq regs A A1 Hr9 Hr91 HA64 ltac:(unfold APPMEM_END in *; lia))).
    subst A1.
    set (W := [(sp - DECLARATION_OF_K, sp); (decl_slot fr, decl_slot fr + 32)]).
    assert (HoutW : forall x, (x < sp - DECLARATION_OF_K \/ sp <= x) -> (x < fr + 2560 \/ fr + 2592 <= x) ->
              outside W x).
    { intros x H1 H2. unfold W, decl_slot. cbn [outside]. split; [lia | split; [lia | exact I]]. }
    assert (Hallapp : all_app W).
    { unfold W. cbn [all_app app_ivl]. split; [|split; [|exact I]].
      - intros a Ha. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
      - intros a Ha. apply Happfr. unfold decl_slot in Ha. lia. }
    assert (HWin : forall x, ~ outside W x ->
              (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr + 24 <= x < fr + FRAME_BYTES) \/
              (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
    { intros x Hx. unfold W, decl_slot in Hx. cbn [outside] in Hx.
      destruct (Z_le_gt_dec (sp - DECLARATION_OF_K) x) as [H1|H1]; destruct (Z_lt_ge_dec x sp) as [H2|H2].
      - left. unfold APPMEM_END in *. lia.
      - right; left. lia.
      - right; left. lia.
      - right; left. lia. }
    assert (HPres : forall x, 0 <= x < 2 ^ 64 -> (exists bb, mbyte rsegs m1 x = Some bb) ->
              exists bb, mbyte rsegs mem' x = Some bb).
    { intros x Hx Hb.
      destruct (rh_out_dec W x) as [Ho|Ho].
      - rewrite !rh_mbyte_mrd in Hb |- *. unfold mrd in *.
        rewrite (MU (wa x)) by (rewrite wa_unsigned by lia; exact Ho). exact Hb.
      - unfold W, decl_slot in Ho. cbn [outside] in Ho. rewrite rh_mbyte_mrd.
        destruct (Z_le_gt_dec (sp - DECLARATION_OF_K) x) as [H1|H1].
        + destruct (Z_lt_ge_dec x sp) as [H2|H2].
          * destruct ST' as (_ & _ & HST). destruct (HST x ltac:(unfold APPMEM_END in *; lia)) as (_ & bb & Hbb).
            exists bb. exact Hbb.
          * destruct HRW as ((_ & HRWb) & _). cbn [cells_bytes cbytes] in HRWb. rewrite app_nil_r in HRWb.
            exact (rh_ba_rd mem' (decl_slot fr) _ x HRWb ltac:(rewrite Hdlen; unfold decl_slot; lia)).
        + destruct HRW as ((_ & HRWb) & _). cbn [cells_bytes cbytes] in HRWb. rewrite app_nil_r in HRWb.
          exact (rh_ba_rd mem' (decl_slot fr) _ x HRWb ltac:(rewrite Hdlen; unfold decl_slot; lia)). }
    destruct (rh_ah B APIf ra g fr (hb1 phi (rnb g 0)) regs m1 mem' md W HFRA1 MU WM HWin HPres)
      as (HAH' & HOWN' & HSTKeq & HSTKHeq).
    assert (HSTKfull : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (rh_stk_keep W m1 mem' _ _ Hwin1 MU WM).
      intros x Hx _. pose proof Hwin1 as (_ & _ & HWw). destruct (HWw x Hx) as (_ & bb & Hbb).
      rewrite <- rh_mbyte_mrd in Hbb |- *.
      exact (HPres x ltac:(lia) (ex_intro _ bb Hbb)). }
    assert (HRO' : ro_agree rsegs mem').
    { apply (rh_ro_keep m1 mem' W Hro1 MU). intros a Ha. pose proof (rh_ro_lt a Ha) as Hlt.
      unfold AC.GT in Hlt. apply HoutW; left; unfold HIGHMEM_BEG in *; lia. }
    assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A)
      by (intros A' HA' HA'r; exact (rh_rg9_eq regs A A' Hr9 HA' HA64 HA'r)).
    assert (HFRAm : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs' mem' md).
    { apply (sl_fr_cl B APIf ra empty FF g fr (hb1 phi (rnb g 0)) regs regs' m1 mem' md W HFRA1 MU WM HRO'
               Hallapp).
      - unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
          RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
          RT_AGLOB, RT_AGLOB_LEN.
        unfold W, decl_slot. cbn [disjoint_from]. unfold HIGHMEM_BEG in HspHM.
        repeat split; first [left; lia | right; lia | exact I].
      - exact HAH'.
      - exact HSTKeq.
      - intros x Hx. apply HoutW; left; unfold HIGHMEM_BEG in *; lia.
      - intros x Hx. apply HoutW; [destruct (Hfrpl DECLARATION_OF_K ltac:(lia)) as [Hc|Hc]; [left | right]; lia | left; lia].
      - intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. apply HoutW; right; lia.
      - intros x Hx. apply HoutW; right; lia.
      - intros x Hx. destruct (Hshin x Hx) as (Hsh' & _).
        unfold W, decl_slot. cbn [outside]. split; [|split; [|exact I]]; intro Hin.
        + apply (app_not_shadow x); [unfold app_mem; right; unfold HIGHMEM_BEG, APPMEM_END in *; lia | exact Hsh'].
        + exact (app_not_shadow x (Happfr x ltac:(lia)) Hsh').
      - intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. apply HoutW; right; lia.
      - eapply fsrec_stklo with (W := W); [exact HAH1 | exact MU |].
        intros x Hx1 Hx2. apply HoutW; lia.
      - intros x Hx.
        destruct (fra_in_apart B APIf ra g fr _ regs m1 md HFRA1 x Hx) as (_ & Hxlo & Hxfr & _).
        apply HoutW; lia.
      - exact HSTKfull.
      - exact Fr2.
      - exact Fr3.
      - exact Fr4.
      - exact Fr8.
      - exact Fr9.
      - exact Fr19.
      - exact Fr26. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs' mem' md')
      by exact (sl_fra_move B APIf ra g fr _ regs' regs' mem' md md' HFRAm
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat).
    assert (HENT' : ENT APIf g (hb1 phi (rnb g 0)) mem' md).
    { apply (ent_store B APIf ra g fr (hb1 phi (rnb g 0)) regs m1 mem' md W HENT1 HFRA1 MU);
        [ | exact HSTKeq | exact HSTKHeq | intros a _ Ho; exact (proj2 (HOWN' a) Ho) ].
      intros x Hx. destruct (rh_out_dec W x) as [Ho|Ho]; [left; exact Ho|].
      destruct (HWin x Ho) as [H|[H|H]]; [right; left; exact H | right; right; left; lia
                                        | right; right; right; exact H]. }
    assert (HENT'' : ENT APIf g (hb1 phi (rnb g 0)) mem' md')
      by exact (ent_mat APIf g (hb1 phi (rnb g 0)) mem' md md' HENT' Hmat).
    (* the facts the exit cut asks for *)
    assert (HoutA : forall x, A <= x < A + 448 -> outside W x)
      by (intros x Hx; apply HoutW; right; lia).
    assert (HoutPhi : forall x, phi <= x < phi + rnb g 0 -> outside W x).
    { intros x Hx. apply HoutW; [left; lia|]. destruct Hblkfr as [Hc|Hc]; [right | left]; lia. }
    assert (HoutFr : forall x, fr <= x < fr + 3136 -> (x < fr + 2560 \/ fr + 2592 <= x) -> outside W x).
    { intros x Hx Hx2. apply HoutW; [|exact Hx2].
      destruct (Hfrpl DECLARATION_OF_K ltac:(lia)) as [Hc|Hc]; [left | right]; lia. }
    assert (HHB' : HB mem' phi (rnb g 0)).
    { destruct HHB1 as (_ & HAphi1).
      split; [exact Hnz0|]. exact (sl_addr_keep m1 mem' W phi (AC.a_size (rnb g 0)) HAphi1 MU Hallapp). }
    assert (HRBE' : RBE g fr regs' mem').
    { apply (rh_RBE_keep g fr regs regs' W m1 mem' A HRBE1 MU Hallapp Hr9 ltac:(lia) HA4 Fr9 HoutA).
      intros x Hx. apply HoutW; left; unfold AC.GT, HIGHMEM_BEG in *; lia. }
    assert (HRF' : RFb g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs' mem').
    { apply (rh_RFb_keep3 g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs regs' W m1 mem' MU
               (rb_RID_len (g_in g) 0) (rb_RFG_len (g_in g) 0 ltac:(lia)) ltac:(lia) HLF);
        [ intros x Hx; apply HoutFr; lia
        | intros x Hx; apply HoutFr; lia
        | intros x Hx; apply HoutFr; lia
        | exact HoutPhi | exact Fr20 | exact Fr22 | exact Fr23 | exact Fr25 | exact HRF1 ]. }
    assert (HDB' : bytes_at rsegs mem' (decl_slot fr) (RcDecl.decl (rt_mb (g_in g)))).
    { destruct HRW as ((_ & HRWb) & _). cbn [cells_bytes cbytes] in HRWb. rewrite app_nil_r in HRWb.
      exact HRWb. }
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists phi, 1, regs', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split; [exact Hgn|].
    split; [exact HRF'|].
    split; [unfold rg; exact Fr10|].
    split; [lia|].
    split; [unfold rg in *; rewrite Fr18; exact H18|].
    split; [exact (rh_spill_keep regs regs' m1 mem' W A 96 _ Hsp96_1 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)
                     Fr9 MU (fun x Hx => HoutA x ltac:(lia)))|].
    split; [exact HDB'|].
    split; [exact HRBE'|].
    split; [unfold rg in *; rewrite Fr21; exact H21|].
    split; [reflexivity|].
    split; [exact HHB'|].
    split; [lia|].
    split; [exact Hdlen|].
    split; [exact (sl_addr_keep m1 mem' W (decl_slot fr) 32 HAD1 MU Hallapp)|].
    unfold rg; rewrite Fr27; exact H27.
Qed.

End S.
