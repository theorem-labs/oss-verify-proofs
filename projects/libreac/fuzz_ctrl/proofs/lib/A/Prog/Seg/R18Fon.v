(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 537 of its 580 lines of code are new or changed and 968 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R18.v, with its module paths, module names and numbers changed; 253 of its 304 lines of code are new or changed and 529 lines of the source are left out. *)
(* lib/A/Prog/Seg/R18Fon.v -- the route (C) twin of Seg/R18F.v's (not in this delivery) footprint run r18_evt_F (image A = fuzz_ctrl.asan,
   libreac v1.9.0, the run [0x81858, 0x818d0) of segment R18).  Written by a Theorem Labs lane,
   single writer of this file.  rule 24: no function proved (stage glue of a walk; kind: segment lemma).

   PROVENANCE.  The text is a Theorem Labs lane's fold blob d8b02189343 of lib/A/Prog/Seg/R18F.v (not in this delivery)
   (`git show 4bae33fdf54:proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R18F.v`, a working branch; the same
   blob as the route (C) walk's, a working branch 1899bed1aee).  Seg/R18F.v (not in this delivery) itself is NOT changed: this is an
   ADDITIVE beside-file.

   THE FORM RULE (L3 brief L3-brief.md (a working note, not in this delivery): a Theorem Labs lane 12:52Z,
   agreed; a Theorem Labs lane approved R18Fon): a run whose premise is a universal `shadow_rw m` gets a twin in which that
   premise is REMOVED if the run neither reads nor stores shadow through it, else NARROWED to the region it reads and
   stores through it, by the callee's own region; the callee in its _on form.

   WHAT IS NARROWED, AND TO WHICH REGION.  r18_evt_F has one universal shadow premise: the `shadow_rw m1` conjunct of
   A.Prog.Seg.R18.r18_pre (Seg/R18.v:452-457), which its caller obligation HPRE concludes (R18F.v:120-124).  Here it is
   r18_pre_on below: r18_pre with that conjunct, and only it, replaced by
     A.ShadowRwOn.shadow_rw_on (A.Prog.declaration_of_c.declaration_of_shadow_R mr D) m1,
   the callee's own region at a0 := mr (the catalogue row) and a1 := D (the declaration slot):
   sh_word_on (mr + 24) 32 \/ sh_word_on (mr + 254) 11 \/ sh_word_on D 32 (declaration_of_c.v:171-173).  The
   callee premise declaration_of_contract_F becomes its _on form
   A.Prog.declaration_of_c.declaration_of_contract_F_on (declaration_of_c.v ffd64306c80 (the blob this tree had at release c5e779efe8c), :210), whose asan premise
   is exactly that region and whose post keeps every region (declaration_of_post_on, :175-185).  Every binder, every
   other premise, their order and the post are r18_evt_F's (R18F.v:88-166).  r18_pre_on_verbatim checks the seven
   other conjuncts of r18_pre_on against r18_pre's by constr_eq.

   WHY THAT REGION, read off R18F.v's proof: the run's ONLY use of the universal premise is HSW, destructed from HPRE
   (R18F.v:209-210), moved to the normalized memory (R18F.v:229) and handed to the callee's asan premise (R18F.v:248).
   The run's own shadow accesses do not use it: the two shadow-byte loads `lb a3,0(a0)` at
   Z.shiftr (mr + 16) 3 + ASAN_K and Z.shiftr (mr + 20) 3 + ASAN_K (R18F.v:181-192) are paid by the ov_read_bytes
   premises R18F.v:112-113, and the four metadata stores at SHv + 320 .. + 323 (R18F.v:196-200) by
   `stk m (SHv + 320) (SHv + 324)` (R18F.v:118).  So the run reads and stores shadow through `shadow_rw m1` only where
   the callee does, and the callee's region is the narrowed premise.  In the proof the one changed step is the move to
   the normalized memory: A.ShadowRwOnT.shadow_rw_on_rel in place of b3n_rel_sw; the call's post is destructed per
   declaration_of_post_on (same conjunct count; the shadow conjunct is not used).

   NAMES.  Every name that has two or more copies in this file's Require closure is written by its full path; there is
   no Module alias (R18F.v's MNF18 is written out as OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF) and no
   global setting.  No Axiom, no Parameter, no unproved step. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YK1j.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import declaration_of_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv AsanRTFacts PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcDecl RcFrag RcSynth.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_rt_b2 Tac_rt2_b2 Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import B3Rtm B3Norm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3FrCl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R18.
(* The evtF form of MemNorm.evt_normalize. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
(* The region form of shadow_rw and its transport across mem_rel (route (C)); Required, not Imported. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT.
(* Last: StepF's step / if_true (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
(* Restore YK11's getr (the register read the statement below is built over), as R18.v does. *)
Import YK11.
Open Scope Z_scope.

(* A.Prog.Seg.R18.r18_pre (Seg/R18.v:452-457) with its sixth conjunct `shadow_rw m1` narrowed to the callee's own
   region at a0 := mr, a1 := D; every other conjunct, and the argument order, r18_pre's. *)
Definition r18_pre_on (m1 : word -> option byte) (A spv mr D : Z) (row : list byte) : Prop :=
  ov_read_bytes rsegs m1 (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 mr)) /\
  stk rsegs m1 (spv - DECLARATION_OF_K) spv /\
  bytes_at rsegs m1 mr row /\
  (exists ob, rw_cells rsegs m1 D [CB 32 ob]) /\
  asan_cells m1 /\
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.shadow_rw_on
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.declaration_of_c.declaration_of_shadow_R mr D) m1 /\
  addressable m1 mr 296 /\ addressable m1 D 32.

(* The pin of r18_pre_on against r18_pre: conjuncts 1-5 and 7-8 are r18_pre's term for term, conjunct 6 is
   r18_pre's `shadow_rw m1` and r18_pre_on's region form (constr_eq: syntactic, not up to conversion). *)
Lemma r18_pre_on_verbatim : forall (m1 : word -> option byte) (A spv mr D : Z) (row : list byte), True.
Proof.
  intros m1 A spv mr D row.
  lazymatch eval cbv beta delta [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R18.r18_pre]
    in (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R18.r18_pre m1 A spv mr D row) with
  | ?c1 /\ ?c2 /\ ?c3 /\ ?c4 /\ ?c5 /\ ?c6 /\ ?c7 /\ ?c8 =>
      lazymatch eval cbv beta delta [r18_pre_on] in (r18_pre_on m1 A spv mr D row) with
      | ?d1 /\ ?d2 /\ ?d3 /\ ?d4 /\ ?d5 /\ ?d6 /\ ?d7 /\ ?d8 =>
          constr_eq c1 d1; constr_eq c2 d2; constr_eq c3 d3; constr_eq c4 d4; constr_eq c5 d5;
          constr_eq c6 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.shadow_rw m1);
          constr_eq d6 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.shadow_rw_on
                          (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.declaration_of_c.declaration_of_shadow_R
                             mr D) m1);
          constr_eq c7 d7; constr_eq c8 d8
      end
  end.
  exact I.
Qed.

(* R18.v's r18_sb / r18_newb / r18_keepb with the goal pattern of evtF (R18F.v:49-86, unchanged). *)
Ltac r18F_sb SHv off STh MUh WMh :=
  let HS := fresh "HSok" in
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
       assert (HS : store_ok rsegs mm (wa (SHv + off)) 1%nat = true)
         by (apply (r18_stk_store_ok mm (SHv + 320) (SHv + 324) (SHv + off) STh); lia)
   end);
  step;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa ?bs) _) =>
       apply (munch_write [(SHv + 320, SHv + 324)] _ mm (SHv + off) bs) in MUh;
         [ | lia
           | rewrite ?length_le1; cbn [length Z.of_nat]; lia
           | rewrite ?length_le1; cbn [inside length Z.of_nat]; left; lia ];
       apply (stk_write rsegs mm (SHv + 320) (SHv + 324) (SHv + off) bs) in STh;
         [ | lia | rewrite ?length_le1; cbn [length Z.of_nat]; lia ];
       apply (wmono_write rsegs _ mm aa bs) in WMh
   end);
  clear HS.

Ltac r18F_newb SHv off Bn :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
      assert (Bn : bytes_at rsegs (write_to_mem mm (wa (SHv + off)) bs) (SHv + off) [Z_to_bv 8 0]) by
        (rewrite <- r18_le1_0;
         apply (bytes_at_write_same rsegs mm (SHv + off) (le1 (Z_to_bv 64 0)));
         [ lia | rewrite ?length_le1; cbn [length Z.of_nat]; lia ])
  end.

Ltac r18F_keepb SHv off Bn :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
      apply (bytes_at_write_other rsegs mm (SHv + off) bs) in Bn;
        [ | lia
          | rewrite ?length_le1; cbn [length Z.of_nat]; lia
          | rewrite ?length_le1; cbn [length Z.of_nat]; lia ]
  end.

(* r18_evt_F (R18F.v:88-166) with its callee premise in the _on form and HPRE concluding r18_pre_on; nothing else
   in the statement differs. *)
Lemma r18_evt_F_on : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.declaration_of_c.declaration_of_contract_F_on ->
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A SHv D mr q v1 v2 : Z) (row : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 SHv -> s10 = Z_to_bv 64 ASAN_K ->
    a0 = Z_to_bv 64 0 ->
    HIGHMEM_BEG + DECLARATION_OF_K <= spv -> spv <= APPMEM_END ->
    0 <= A -> A + 312 <= 2 ^ 64 ->
    0 <= mr -> mr + 296 <= 2 ^ 31 -> mr mod 8 = 0 ->
    6283264 <= SHv -> SHv + 324 <= 2 ^ 64 ->
    0 <= q -> q + 8 <= 2 ^ 64 ->
    6283264 <= D -> D + 32 <= 2 ^ 64 ->
    (D + 32 <= mr \/ mr + 296 <= D) ->
    (mr + 296 <= spv - DECLARATION_OF_K \/ spv <= mr) ->
    (D + 32 <= spv - DECLARATION_OF_K \/ spv <= D) ->
    (SHv + 324 <= spv - DECLARATION_OF_K \/ spv <= SHv + 320) ->
    (SHv + 324 <= D \/ D + 32 <= SHv + 320) ->
    (D + 32 <= RT_LO \/ RT_HI <= D) -> app_mem (D + 32) ->
    length row = 296%nat -> RcDecl.decl_ok row = true ->
    ov_read_bytes rsegs m (wa (A + 200)) 8 = Some (le8 (Z_to_bv 64 D)) ->
    ov_read_bytes rsegs m (wa (A + 8)) 8 = Some (le8 (Z_to_bv 64 (mr + 16))) ->
    ov_read_bytes rsegs m (wa (A + 0)) 8 = Some (le8 (Z_to_bv 64 (mr + 20))) ->
    ov_read_bytes rsegs m (wa (A + 216)) 8 = Some (le8 (Z_to_bv 64 q)) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 16) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 20) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa q) 4 = Some (le4 (Z_to_bv 64 v1)) ->
    ov_read_bytes rsegs m (wa (q + 4)) 4 = Some (le4 (Z_to_bv 64 v2)) ->
    ov_read_bytes rsegs m (wa (mr + 16)) 4 = Some (le4 (Z_to_bv 64 v1)) ->
    ov_read_bytes rsegs m (wa (mr + 20)) 4 = Some (le4 (Z_to_bv 64 v2)) ->
    stk rsegs m (SHv + 320) (SHv + 324) ->
    ro_agree rsegs m ->
    (forall m1, munch [(SHv + 320, SHv + 324)] m m1 -> wmono rsegs m m1 ->
       stk rsegs m1 (SHv + 320) (SHv + 324) -> ro_agree rsegs m1 ->
       bytes_at rsegs m1 (SHv + 320) [Z_to_bv 8 0] -> bytes_at rsegs m1 (SHv + 321) [Z_to_bv 8 0] ->
       bytes_at rsegs m1 (SHv + 322) [Z_to_bv 8 0] -> bytes_at rsegs m1 (SHv + 323) [Z_to_bv 8 0] ->
       r18_pre_on m1 A spv mr D row) ->
    (* the segment's own accesses, one per load, the four metadata stores as one range *)
    rng RNG (A + 200) 8 ->
    rng RNG (A + 8) 8 ->
    rng RNG (Z.shiftr (mr + 16) 3 + ASAN_K) 1 ->
    rng RNG (A + 216) 8 ->
    rng RNG q 4 ->
    rng RNG (mr + 16) 4 ->
    rng RNG (A + 0) 8 ->
    rng RNG (Z.shiftr (mr + 20) 3 + ASAN_K) 1 ->
    rng RNG (q + 4) 4 ->
    rng RNG (mr + 20) 4 ->
    rng RNG (SHv + 320) 4 ->
    rng RNG (A + 112) 8 ->
    (* the callee's regions (declaration_of_contract_F_on's rng premises, a0 := mr, a1 := D) *)
    rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (spv - DECLARATION_OF_K) DECLARATION_OF_K ->
    sh_word_rng RNG (spv - DECLARATION_OF_K) DECLARATION_OF_K ->
    rng RNG RT_LO (RT_HI - RT_LO) ->
    rng RNG mr 296 ->
    rng RNG ((mr / 8 + ASAN_K) / 8 * 8)
            (((mr + 295) / 8 + ASAN_K) / 8 * 8 + 8 - (mr / 8 + ASAN_K) / 8 * 8) ->
    rng RNG D 32 ->
    rng RNG ((D / 8 + ASAN_K) / 8 * 8)
            (((D + 31) / 8 + ASAN_K) / 8 * 8 + 8 - (D / 8 + ASAN_K) / 8 * 8) ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m1 m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x818d0) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         getr R 18 = Z_to_bv 64 D /\ getr R 10 = Z_to_bv 64 1 /\
         munch [(SHv + 320, SHv + 324)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 (SHv + 320) (SHv + 324) /\
         munch [(spv - DECLARATION_OF_K, spv); (D, D + 32)] m1 m' /\ wmono rsegs m1 m' /\
         stk rsegs m' (spv - DECLARATION_OF_K) spv /\
         rw_cells rsegs m' D [CB 32 (RcDecl.decl row)] /\
         bytes_at rsegs m' mr row /\
         bytes_at rsegs m' (SHv + 320) [Z_to_bv 8 0] /\ bytes_at rsegs m' (SHv + 321) [Z_to_bv 8 0] /\
         bytes_at rsegs m' (SHv + 322) [Z_to_bv 8 0] /\ bytes_at rsegs m' (SHv + 323) [Z_to_bv 8 0])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81858) fc None m (seg_rom rsegs)).
Proof.
  intros DCF RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A SHv D mr q v1 v2 row -> -> -> -> -> Hsplo Hsphi HA0 HAb Hmr0 Hmrb Hmr8 HSH0 HSHb
    Hq0 Hqb HD0 HDb Hdm Hmsp Hdsp Hshsp Hshd Hrt Hdapp Hrowlen Hdecl
    R192 R16 R8 R216 K16 K20 Q1 Q2 M16 M20 ST HRO HPRE
    G200 G8 GK16 G216 GQ1 GM16 G0 GK20 GQ2 GM20 GSH G112
    CBY CIMG CWIN CWINS CRT CROW CROWS COUT COUTS.
  assert (Hspv : 0 <= spv < 2 ^ 64) by (unfold HIGHMEM_BEG, DECLARATION_OF_K, APPMEM_END in *; lia).
  pose proof (munch_refl [(SHv + 320, SHv + 324)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 81858 ld s2,200(s1) ; 8185c beqz a0,81864 (taken) *)
  step. step. if_true.
  (* 81864 ld a4,8(s1) ; 81868 srli a0,a4,3 ; 8186c add a0,a0,s10 *)
  step. step. step. r18_shfix.
  (* 81870 lb a3,0(a0) ; 81874 ld a0,216(s1) ; 81878 lw a0,0(a0) *)
  step. step. step.
  (* 8187c bnez a3,81960 (not taken) *)
  step. first [ if_false | if_false_by r18_nz0 ].
  (* 81880 lw a2,0(a4) ; 81884 beq a0,a2,8188c (taken) *)
  step. step. if_true_by (r18_eqb_refl (sx32 (Z_to_bv 64 v1))).
  (* 8188c ld a4,0(s1) ; 81890 srli ; 81894 add *)
  step. step. step. r18_shfix.
  (* 81898 lb a3,0(a0) ; 8189c ld a0,216(s1) ; 818a0 lw a0,4(a0) *)
  step. step. step.
  (* 818a4 bnez a3,81970 (not taken) *)
  step. first [ if_false | if_false_by r18_nz0 ].
  (* 818a8 lw a2,0(a4) ; 818ac beq a0,a2,818b4 (taken) *)
  step. step. if_true_by (r18_eqb_refl (sx32 (Z_to_bv 64 v2))).
  (* 818b4 .. 818c0 : the four metadata stores *)
  r18F_sb SHv 320 ST MU WM. r18F_newb SHv 320 B0.
  r18F_sb SHv 321 ST MU WM. r18F_keepb SHv 321 B0. r18F_newb SHv 321 B1.
  r18F_sb SHv 322 ST MU WM. r18F_keepb SHv 322 B0. r18F_keepb SHv 322 B1. r18F_newb SHv 322 B2.
  r18F_sb SHv 323 ST MU WM. r18F_keepb SHv 323 B0. r18F_keepb SHv 323 B1. r18F_keepb SHv 323 B2.
  r18F_newb SHv 323 B3.
  (* the four stores wrote metadata bytes only, above every read-only address *)
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MI : ro_agree rsegs mm)
        by (apply (r18_ro_keep m mm [(SHv + 320, SHv + 324)] HRO MU); intros x Hx;
            pose proof (r18_ro_lt x Hx) as Hlt; cbn [outside]; split; [lia | exact I])
  end.
  (* 818c4 ld a0,112(s1) ; 818c8 mv a1,s2 ; 818cc jal declaration_of *)
  destruct (HPRE _ MU WM ST MI B0 B1 B2 B3)
    as (R112 & STc & HROW & (ob & HOB) & HAC & HSW & HAmr & HAD).
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      change (ov_read_bytes rsegs mm (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 mr))) in R112
  end.
  step. step. step.
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm)
  end.
  (* declaration_of runs on the normalized memory, which has the mem_inv its contract asks for *)
  pose proof (mem_rel_normalize rsegs m1 MI) as REL.
  assert (STc0 : stk rsegs (normalize rsegs m1) (spv - DECLARATION_OF_K) spv)
    by exact (proj1 (b3n_rel_stk m1 (normalize rsegs m1) (spv - DECLARATION_OF_K) spv REL
                       ltac:(unfold HIGHMEM_BEG, DECLARATION_OF_K in *; lia) ltac:(lia)) STc).
  assert (HROW0 : bytes_at rsegs (normalize rsegs m1) mr row)
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) HROW).
  assert (HOB0 : rw_cells rsegs (normalize rsegs m1) D [CB 32 ob])
    by exact (proj1 (r18_rel_rw m1 (normalize rsegs m1) D _ REL ltac:(lia)) HOB).
  assert (HAC0 : asan_cells (normalize rsegs m1)) by exact (proj1 (b3n_rel_cells m1 _ REL) HAC).
  (* the one changed step: the callee's region moves to the normalized memory by the region transport *)
  assert (HSW0 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.shadow_rw_on
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.declaration_of_c.declaration_of_shadow_R
                      mr D) (normalize rsegs m1))
    by exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.shadow_rw_on_rel _ m1 _ REL HSW).
  assert (HAmr0 : addressable (normalize rsegs m1) mr 296) by exact (proj1 (b3n_rel_ad m1 _ _ _ REL) HAmr).
  assert (HAD0 : addressable (normalize rsegs m1) D 32) by exact (proj1 (b3n_rel_ad m1 _ _ _ REL) HAD).
  eapply evtF_mono.
  { eapply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.evtF_normalize_ro RNG _ _ _ _ _ _ _ _ MI).
    eapply DCF with (lo := spv - DECLARATION_OF_K) (row := row) (ob := ob);
      rewrite ?(lib.Lib.MState.unsigned_lit spv) by lia; rewrite ?(lib.Lib.MState.unsigned_lit mr) by lia;
      rewrite ?(lib.Lib.MState.unsigned_lit D) by lia.
    - exact STc0.
    - lia.
    - exact Hmr8.
    - exact Hrowlen.
    - exact HROW0.
    - exact HOB0.
    - exact Hdm.
    - exact Hmsp.
    - exact Hdsp.
    - exact (mem_inv_normalize rsegs m1).
    - exact HAC0.
    - exact HSW0.
    - unfold HIGHMEM_BEG, DECLARATION_OF_K in *; lia.
    - lia.
    - exact HAmr0.
    - exact HAD0.
    - exact Hdapp.
    - exact Hrt.
    - exact CBY.
    - exact CIMG.
    - exact CWIN.
    - exact CWINS.
    - exact CRT.
    - exact CROW.
    - exact CROWS.
    - exact COUT.
    - exact COUTS. }
  intros ms' (s0' & PO & HREL & HROS). unfold declaration_of_post_on in PO. rewrite Hdecl in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MUc0 & WMc0 & _ & STq0 & HRW0 & HROWq0 & _ & _).
  subst s0'.
  destruct HREL as (ERg & EF & EP & ES & EV & EC & ERo & HMR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ERg, EF, EP, ES, EV, EC, ERo,
    HMR.
  pose proof (b3n_ms_eta ms' ES) as Ems.
  rewrite ERg, EF, EP, EC, EV, ERo in Ems.
  lazymatch type of Ems with
  | context [ret_pc (Z_to_bv 64 ?k)] =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) in Ems by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  remember (ms_mem ms') as m' eqn:Em'. clear Em'.
  rewrite ?(lib.Lib.MState.unsigned_lit spv) in MUc0, STq0 by lia.
  rewrite ?(lib.Lib.MState.unsigned_lit D) in MUc0, HRW0 by lia.
  rewrite ?(lib.Lib.MState.unsigned_lit mr) in HROWq0 by lia.
  (* the post on the real memory *)
  assert (MUc : munch [(spv - DECLARATION_OF_K, spv); (D, D + 32)] m1 m')
    by exact (b3n_rel_munch _ m1 _ m' m0' REL HMR MUc0 HROS).
  assert (WMc : wmono rsegs m1 m').
  { apply (b3n_rel_wmono [(spv - DECLARATION_OF_K, spv); (D, D + 32)] m1 _ m' m0' REL HMR MUc WMc0).
    intros x E0. apply (b3n_W_ro _ x); [|exact E0].
    intros p Hp. cbn [In] in Hp. destruct Hp as [<-|[<-|[]]]; cbn [fst];
      unfold HIGHMEM_BEG, DECLARATION_OF_K in *; lia. }
  assert (STq : stk rsegs m' (spv - DECLARATION_OF_K) spv)
    by exact (proj2 (b3n_rel_stk m' m0' (spv - DECLARATION_OF_K) spv HMR
                       ltac:(unfold HIGHMEM_BEG, DECLARATION_OF_K in *; lia) ltac:(lia)) STq0).
  assert (HRW : rw_cells rsegs m' D [CB 32 (RcDecl.decl row)])
    by exact (proj2 (r18_rel_rw m' m0' D _ HMR ltac:(lia)) HRW0).
  assert (HROWq : bytes_at rsegs m' mr row) by exact (proj2 (bytes_at_rel rsegs m' m0' _ _ HMR) HROWq0).
  assert (HOUTD : forall k, 0 <= k < 4 ->
            disjoint_from [(spv - DECLARATION_OF_K, spv); (D, D + 32)] (SHv + 320 + k) 1).
  { intros k Hk. cbn [disjoint_from]. split; [|split; [|exact I]]; lia. }
  assert (HB0 : bytes_at rsegs m' (SHv + 320) [Z_to_bv 8 0]).
  { apply (bytes_at_transport rsegs _ _ m' (SHv + 320) [Z_to_bv 8 0] B0 MUc).
    cbn [length Z.of_nat]. replace (SHv + 320) with (SHv + 320 + 0) by lia. exact (HOUTD 0 ltac:(lia)). }
  assert (HB1 : bytes_at rsegs m' (SHv + 321) [Z_to_bv 8 0]).
  { apply (bytes_at_transport rsegs _ _ m' (SHv + 321) [Z_to_bv 8 0] B1 MUc).
    cbn [length Z.of_nat]. replace (SHv + 321) with (SHv + 320 + 1) by lia. exact (HOUTD 1 ltac:(lia)). }
  assert (HB2 : bytes_at rsegs m' (SHv + 322) [Z_to_bv 8 0]).
  { apply (bytes_at_transport rsegs _ _ m' (SHv + 322) [Z_to_bv 8 0] B2 MUc).
    cbn [length Z.of_nat]. replace (SHv + 322) with (SHv + 320 + 2) by lia. exact (HOUTD 2 ltac:(lia)). }
  assert (HB3 : bytes_at rsegs m' (SHv + 323) [Z_to_bv 8 0]).
  { apply (bytes_at_transport rsegs _ _ m' (SHv + 323) [Z_to_bv 8 0] B3 MUc).
    cbn [length Z.of_nat]. replace (SHv + 323) with (SHv + 320 + 3) by lia. exact (HOUTD 3 ltac:(lia)). }
  do 3 eexists. split; [exact Ems|].
  do 15 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|].
  split; [exact MUc|]. split; [exact WMc|]. split; [exact STq|].
  split; [exact HRW|]. split; [exact HROWq|].
  split; [exact HB0|]. split; [exact HB1|]. split; [exact HB2 | exact HB3].
Qed.

Print Assumptions r18_evt_F_on.
