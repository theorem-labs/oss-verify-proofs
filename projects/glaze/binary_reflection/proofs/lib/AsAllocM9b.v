(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8m.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Lemma rdn_wbytes_hit4 : forall segs (m : word -> option byte) (a : word) z,
  (bv_unsigned a + 4 <= 2 ^ 64)%Z -> rdn segs (wbytes m a (LE4 z)) a 4 = Some (LE4 z).
Proof.
  intros segs m a z Ha. pose proof (rdn_wbytes_hit segs (LE4 z) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Ha.
Qed.

(* [comment removed for export] *)
Ltac sltu0 :=
  match goal with |- context [v_sltu ?a ?b] =>
    replace (v_sltu a b) with (Z_to_bv 64 0)
      by (symmetry; rwH; (lazymatch goal with |- ?G => let G' := eval unfold v_sltu in G in change_no_check G' end); rewrite c_ltu_ltb; unorm; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity) end.

Ltac av_and F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_and_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition mfi_clob : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

(* [comment removed for export] *)
Definition mfi_m0 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v addr size : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 (Z_to_bv 64 0x8a6b4)))
    (at_ sp (-48)) (LE8 size))
    (at_ sp (-56)) (LE8 addr))
    (at_ sp (-64)) (LE8 s2v))
    (at_ sp (-72)) (LE8 s3v))
    (at_ sp (-80)) (LE8 s4v).
Definition mfi_m1 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v addr size name : word) (PGP : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (mfi_m0 mem sp ra s0v s1v s2v s3v s4v addr size)
    (at_ sp (-128)) (LE4 50))
    (at_ sp (-136)) (LE8 (Z_to_bv 64 0x824e0)))
    (at_ sp (-144)) (LE8 size))
    (at_ sp (-152)) (LE8 (Z_to_bv 64 1)))
    (at_ sp (-160)) (LE8 addr))
    (at_ sp (-168)) (LE8 name))
    (at_ sp (-176)) (LE8 (Z_to_bv 64 PGP)))
    (at_ sp (-184)) (LE8 s5v).
#[local] Hint Unfold mfi_m0 mfi_m1 : asfr.

Section MFIPRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v addr size name : word) (PGP CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H11 : getr regs 11 = addr.
  Hypothesis H12 : getr regs 12 = size.
  Hypothesis H13 : getr regs 13 = name.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Haddr : (U addr mod 4096 = 0)%Z.
  Hypothesis Hsize : (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63)%Z.
  Hypothesis Hname : (U name <> 0)%Z.
  Hypothesis HPGP : (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI)%Z.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ sp (-400)) 400 = true.
  Hypothesis Rgpg : rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn ASEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].

  #[local] Abbreviation M1 := (mfi_m1 mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP).

  Lemma mfi_pre :
    exists r, msteps ASEGS (mkst regs (0x8a688 : word) mem rom) (mkst r (0x8073c : word) M1 rom)
      /\ getr r 1 = Z_to_bv 64 0x824fc /\ getr r 2 = at_ sp (-128)
      /\ getr r 8 = size /\ getr r 9 = Z_to_bv 64 1 /\ getr r 18 = addr /\ getr r 19 = name /\ getr r 20 = Z_to_bv 64 PGP
      /\ getr r 10 = addr /\ getr r 11 = size /\ getr r 12 = Z_to_bv 64 3 /\ getr r 13 = Z_to_bv 64 50
      /\ getr r 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr r 15 = Z_to_bv 64 0 /\ getr r 17 = Z_to_bv 64 222
      /\ regs_agree (fun i : reg => In i (1%bv :: 2%bv :: 8%bv :: 9%bv :: 18%bv :: 19%bv :: 20%bv :: mfi_clob)) regs r.
  Proof using Rdpm Rgcf Rpg Rgpg Hstk HCF HPGP Hname Hsize Haddr Hsp H21 H20 H19 H18 H9 H8 H13 H12 H11 H2 H1 CF.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range addr) as Har. pose proof (u64_range size) as Hsr. pose proof (u64_range name) as Hnr.
    destruct Hsize as [Hsz1 Hsz2].
    wd_eexists. split.
    - an F_8a680 D_8a680.                              (* [comment removed for export] *)
      fsd F_8a684 D_8a684 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8a688 D_8a688 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_8a68c D_8a68c (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_8a690 D_8a690 (at_ sp (-32)).              (* [comment removed for export] *)
      an F_8a694 D_8a694.                              (* [comment removed for export] *)
      an F_8a698 D_8a698.                              (* [comment removed for export] *)
      an F_8a69c D_8a69c.                              (* [comment removed for export] *)
      an F_8a6a0 D_8a6a0.                              (* [comment removed for export] *)
      an F_8a6a4 D_8a6a4.                              (* [comment removed for export] *)
      an F_8a6a8 D_8a6a8.                              (* [comment removed for export] *)
      an F_825c0 D_825c0.                              (* [comment removed for export] *)
      an F_825c4 D_825c4.                              (* [comment removed for export] *)
      an F_825c8 D_825c8.                              (* [comment removed for export] *)
      an F_82448 D_82448.                              (* [comment removed for export] *)
      fsd F_8244c D_8244c (at_ sp (-40)).              (* [comment removed for export] *)
      fsd F_82450 D_82450 (at_ sp (-48)).              (* [comment removed for export] *)
      fsd F_82454 D_82454 (at_ sp (-56)).              (* [comment removed for export] *)
      fsd F_82458 D_82458 (at_ sp (-64)).              (* [comment removed for export] *)
      fsd F_8245c D_8245c (at_ sp (-72)).              (* [comment removed for export] *)
      fsd F_82460 D_82460 (at_ sp (-80)).              (* [comment removed for export] *)
      an F_82464 D_82464.                              (* [comment removed for export] *)
      an F_82468 D_82468.                              (* [comment removed for export] *)
      an F_8246c D_8246c.                              (* [comment removed for export] *)
      an F_82470 D_82470.                              (* [comment removed for export] *)
      cld8 F_82474 D_82474 (Z_to_bv 64 PGP) Rgpg.      (* [comment removed for export] *)
      cld8 F_82478 D_82478 (Z_to_bv 64 4096) Rpg.      (* [comment removed for export] *)
      an F_8247c D_8247c.                              (* [comment removed for export] *)
      ab_tk F_82480 D_82480 ltac:(condz).              (* [comment removed for export] *)
      an F_82490 D_82490.                              (* [comment removed for export] *)
      an F_82494 D_82494.                              (* [comment removed for export] *)
      ab_ft F_82498 D_82498 ltac:(condz).              (* [comment removed for export] *)
      av F_8249c D_8249c (Z_to_bv 64 (U size + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_824a0 D_824a0 (Z_to_bv 64 (U size + 4095)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_824a4 D_824a4 (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av_and F_824a8 D_824a8 size
        ltac:(rewrite v_and_m4k; unorm; replace (U size + 4095 - (U size + 4095) mod 4096)%Z with (U size) by (Z.div_mod_to_equations; lia); apply Z_to_bv_bv_unsigned).   (* [comment removed for export] *)
      ab_tk F_824ac D_824ac ltac:(condz).              (* [comment removed for export] *)
      av_and F_824bc D_824bc addr
        ltac:(rewrite v_and_m4k; replace (U addr - U addr mod 4096)%Z with (U addr) by lia; apply Z_to_bv_bv_unsigned).   (* [comment removed for export] *)
      an F_824c0 D_824c0.                              (* [comment removed for export] *)
      fsw F_824c4 D_824c4 (at_ sp (-128)).             (* [comment removed for export] *)
      an F_824c8 D_824c8.                              (* [comment removed for export] *)
      an F_824cc D_824cc.                              (* [comment removed for export] *)
      an F_824d0 D_824d0.                              (* [comment removed for export] *)
      an F_824d4 D_824d4.                              (* [comment removed for export] *)
      an F_82adc D_82adc.                              (* [comment removed for export] *)
      fsd F_82ae0 D_82ae0 (at_ sp (-136)).             (* [comment removed for export] *)
      fsd F_82ae4 D_82ae4 (at_ sp (-144)).             (* [comment removed for export] *)
      fsd F_82ae8 D_82ae8 (at_ sp (-152)).             (* [comment removed for export] *)
      fsd F_82aec D_82aec (at_ sp (-160)).             (* [comment removed for export] *)
      fsd F_82af0 D_82af0 (at_ sp (-168)).             (* [comment removed for export] *)
      fsd F_82af4 D_82af4 (at_ sp (-176)).             (* [comment removed for export] *)
      fsd F_82af8 D_82af8 (at_ sp (-184)).             (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
      an F_82afc D_82afc.                              (* [comment removed for export] *)
      an F_82b00 D_82b00.                              (* [comment removed for export] *)
      ab_ft F_82b04 D_82b04 ltac:(condz).              (* [comment removed for export] *)
      an F_82b08 D_82b08.                              (* [comment removed for export] *)
      an F_82b0c D_82b0c.                              (* [comment removed for export] *)
      cld8 F_82b10 D_82b10 (Z_to_bv 64 CF) Rgcf.       (* [comment removed for export] *)
      clbu F_82b14 D_82b14 (Z_to_bv 8 0) Rdpm.         (* [comment removed for export] *)
      an F_82b18 D_82b18.                              (* [comment removed for export] *)
      ab_tk F_82b1c D_82b1c ltac:(condz).              (* [comment removed for export] *)
      an F_82c2c D_82c2c.                              (* [comment removed for export] *)
      fld F_82c30 D_82c30 (Z_to_bv 64 0x824e0).        (* [comment removed for export] *)
      fld F_82c34 D_82c34 size.                        (* [comment removed for export] *)
      fld F_82c38 D_82c38 (Z_to_bv 64 1).              (* [comment removed for export] *)
      fld F_82c3c D_82c3c addr.                        (* [comment removed for export] *)
      fld F_82c40 D_82c40 name.                        (* [comment removed for export] *)
      fld F_82c44 D_82c44 (Z_to_bv 64 PGP).            (* [comment removed for export] *)
      fld F_82c48 D_82c48 s5v.                         (* [comment removed for export] *)
      an F_82c4c D_82c4c.                              (* [comment removed for export] *)
      rt F_82c50 D_82c50.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 50) (v := Z_to_bv 64 50);
          [exact F_824d8 | reflexivity | exact D_824d8
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold mfi_m1 in G in change_no_check G' end);
            repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]);
            apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
          | reflexivity]
        | step_simpl]; rewrite (v_lw_small 50) by lia; vn.   (* [comment removed for export] *)
      an F_824dc D_824dc.                              (* [comment removed for export] *)
      an F_824e0 D_824e0.                              (* [comment removed for export] *)
      an F_824e4 D_824e4.                              (* [comment removed for export] *)
      an F_824e8 D_824e8.                              (* [comment removed for export] *)
      an F_824ec D_824ec.                              (* [comment removed for export] *)
      an F_824f0 D_824f0.                              (* [comment removed for export] *)
      an F_80730 D_80730.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma mfi_m1_outside : forall x : word, (U x < U sp - 400 \/ U sp <= U x)%Z -> M1 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mfi_m1, mfi_m0 in G in change_no_check G' end).
    repeat (rewrite wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma mfi_m1_grows : mem_grows mem M1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mfi_m1, mfi_m0 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma mfi_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, Z_to_bv 64 0x8a6b4); (-48, size); (-56, addr); (-64, s2v);
               (-72, s3v); (-80, s4v)]%Z -> rdn ASEGS M1 (at_ sp k) 8 = Some (LE8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mfi_m1, mfi_m0 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
End MFIPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MFIPOST.
  Variables (M2 rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v addr size name : word) (PGP CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x824fc.
  Hypothesis H2 : getr regs 2 = at_ sp (-128).
  Hypothesis H8 : getr regs 8 = size.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 1.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hsok : store_ok ASEGS M2 (at_ sp (-84)) 4 = true.
  Hypothesis S_ra : rdn ASEGS M2 (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS M2 (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS M2 (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS M2 (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_cra : rdn ASEGS M2 (at_ sp (-40)) 8 = Some (LE8 (Z_to_bv 64 0x8a6b4)).
  Hypothesis S_c0 : rdn ASEGS M2 (at_ sp (-48)) 8 = Some (LE8 size).
  Hypothesis S_c1 : rdn ASEGS M2 (at_ sp (-56)) 8 = Some (LE8 addr).
  Hypothesis S_c2 : rdn ASEGS M2 (at_ sp (-64)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn ASEGS M2 (at_ sp (-72)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn ASEGS M2 (at_ sp (-80)) 8 = Some (LE8 s4v).

  Definition mfi_clob2 : list reg := 1%bv :: 2%bv :: 8%bv :: 9%bv :: 18%bv :: 19%bv :: 20%bv :: mfi_clob.

  (* [comment removed for export] *)
  Section OK.
    Hypothesis H10 : getr regs 10 = addr.
    Hypothesis Haddr : (U addr < 2 ^ 63)%Z.
    Hypothesis Hanz : (0 < U addr)%Z.
    Hypothesis Rgcf : rdn ASEGS M2 (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)).
    Hypothesis Rlim : rdn ASEGS M2 (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
    Lemma mfi_ok :
      exists r, msteps ASEGS (mkst regs (0x80740 : word) M2 rom)
                             (mkst r ra (wbytes M2 (at_ sp (-84)) (LE4 0xffffffffaaaaaaaa)) rom)
        /\ getr r 10 = addr /\ getr r 2 = sp /\ getr r 1 = ra
        /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
        /\ regs_agree (fun i : reg => In i mfi_clob2) regs r.
    Proof using Rlim Rgcf Hanz Haddr H10 S_s4 S_s3 S_c2 S_c1 S_c0 S_cra S_s2 S_s1 S_s0 S_ra Hsok HCF Hret Hsp H8 H2 H1 CF size.
      pose proof (u64_range sp) as Hspr. pose proof (u64_range addr) as Har.
      wd_eexists. split.
      - rt F_80738 D_80738.                            (* [comment removed for export] *)
        an F_824f4 D_824f4.                            (* [comment removed for export] *)
        an F_824f8 D_824f8.                            (* [comment removed for export] *)
        an F_824fc D_824fc.                            (* [comment removed for export] *)
        an F_80710 D_80710.                            (* [comment removed for export] *)
        an F_80714 D_80714.                            (* [comment removed for export] *)
        ab_tk F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
        an F_80728 D_80728. sltu0.                     (* [comment removed for export] *)
        rt F_8072c D_8072c.                            (* [comment removed for export] *)
        an F_82500 D_82500.                            (* [comment removed for export] *)
        an F_82504 D_82504.                            (* [comment removed for export] *)
        fsw F_82508 D_82508 (at_ sp (-84)).            (* [comment removed for export] *)
        an F_8250c D_8250c.                            (* [comment removed for export] *)
        an F_82510 D_82510.                            (* [comment removed for export] *)
        an F_82514 D_82514.                            (* [comment removed for export] *)
        an F_80710 D_80710.                            (* [comment removed for export] *)
        an F_80714 D_80714.                            (* [comment removed for export] *)
        ab_tk F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
        an F_80728 D_80728. sltu0.                     (* [comment removed for export] *)
        rt F_8072c D_8072c.                            (* [comment removed for export] *)
        ab_ft F_82518 D_82518 ltac:(condz).            (* [comment removed for export] *)
        an F_8251c D_8251c.                            (* [comment removed for export] *)
        an F_82520 D_82520.                            (* [comment removed for export] *)
        an F_7c614 D_7c614.                            (* [comment removed for export] *)
        cld8 F_7c618 D_7c618 (Z_to_bv 64 CF) Rgcf.     (* [comment removed for export] *)
        cld8 F_7c61c D_7c61c (Z_to_bv 64 0) Rlim.      (* [comment removed for export] *)
        ab_tk F_7c620 D_7c620 ltac:(condz).            (* [comment removed for export] *)
        rt F_7c63c D_7c63c.                            (* [comment removed for export] *)
        an F_82524 D_82524.                            (* [comment removed for export] *)
        cld8 F_82528 D_82528 (Z_to_bv 64 0x8a6b4) S_cra.   (* [comment removed for export] *)
        cld8 F_8252c D_8252c size S_c0.                (* [comment removed for export] *)
        cld8 F_82530 D_82530 addr S_c1.                (* [comment removed for export] *)
        cld8 F_82534 D_82534 s2v S_c2.                 (* [comment removed for export] *)
        cld8 F_82538 D_82538 s3v S_s3.                 (* [comment removed for export] *)
        cld8 F_8253c D_8253c s4v S_s4.                 (* [comment removed for export] *)
        an F_82540 D_82540.                            (* [comment removed for export] *)
        rt F_82544 D_82544.                            (* [comment removed for export] *)
        ab_ft F_8a6ac D_8a6ac ltac:(condz).            (* [comment removed for export] *)
        cld8 F_8a6b0 D_8a6b0 ra S_ra.                  (* [comment removed for export] *)
        cld8 F_8a6b4 D_8a6b4 s0v S_s0.                 (* [comment removed for export] *)
        cld8 F_8a6b8 D_8a6b8 s1v S_s1.                 (* [comment removed for export] *)
        cld8 F_8a6bc D_8a6bc s2v S_s2.                 (* [comment removed for export] *)
        an F_8a6c0 D_8a6c0.                            (* [comment removed for export] *)
        aret F_8a6c4 D_8a6c4 ra.                       (* [comment removed for export] *)
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End OK.
End MFIPOST.
End FPGen.
End AsAllocM8m.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM9a.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Lemma land_m8 : forall a, (0 <= a < 2 ^ 64)%Z -> Z.land a (2 ^ 64 - 2 ^ 3) = (a - a mod 2 ^ 3)%Z.
Proof.
  intros a Ha.
  replace (2 ^ 64 - 2 ^ 3)%Z with (Z.ldiff (Z.ones 64) (Z.ones 3)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod a (2 ^ 3) ltac:(lia)). lia.
Qed.
Lemma v_andi_m8 : forall x, (0 <= x < 2 ^ 64)%Z -> v_andi (Z_to_bv 64 x) (-8) = Z_to_bv 64 (x - x mod 8).
Proof.
  intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). rewrite u_Z2bv by lia. change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3)%Z.
  rewrite land_m8 by lia. reflexivity.
Qed.
Lemma v_and_4095_al : forall mb, (0 <= mb < 2 ^ 64)%Z -> (mb mod 4096 = 0)%Z -> v_and (Z_to_bv 64 4095) (Z_to_bv 64 mb) = Z_to_bv 64 0.
Proof.
  intros mb Hmb Hal. (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). rewrite !u_Z2bv by lia. f_equal. rewrite Z.land_comm.
  change 4095%Z with (Z.ones 12). rewrite Z.land_ones by lia. exact Hal.
Qed.
Lemma v_and_7_al : forall x, (0 <= x < 2 ^ 64)%Z -> (x mod 8 = 0)%Z -> v_and (Z_to_bv 64 x) (Z_to_bv 64 7) = Z_to_bv 64 0.
Proof.
  intros x Hx Hal. (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). rewrite !u_Z2bv by lia. f_equal. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. exact Hal.
Qed.

(* [comment removed for export] *)
Definition la_msz (size : Z) : Z := ((size + 4095) / 4096 * 4096 + 4096)%Z.

Section FPGen.
Context {fx : FPState}.

Definition la_m0 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 s3v))
    (at_ sp (-48)) (LE8 s4v))
    (at_ sp (-56)) (LE8 s5v))
    (at_ sp (-64)) (LE8 s6v))
    (at_ sp (-72)) (LE8 s7v))
    (at_ sp (-80)) (LE8 s8v))
    (at_ sp (-88)) (LE8 s9v).
#[local] Hint Unfold la_m0 : asfr.

(* [comment removed for export] *)
Definition la_regs (sp stats : word) (size : Z) (r : bvmap 5 word) : Prop :=
  getr r 2 = at_ sp (-96) /\ getr r 8 = stats /\ getr r 9 = Z_to_bv 64 (0x103f18 + 64)
  /\ getr r 18 = Z_to_bv 64 (la_msz size) /\ getr r 19 = Z_to_bv 64 size /\ getr r 24 = Z_to_bv 64 7.

Section PRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v stats name : word) (size : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (0x103f18 + 64).
  Hypothesis H11 : getr regs 11 = stats.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 size.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 8.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v. Hypothesis H23 : getr regs 23 = s7v. Hypothesis H24 : getr regs 24 = s8v.
  Hypothesis H25 : getr regs 25 = s9v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ sp (-96)) 96 = true.
  Hypothesis C_pg : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_gnm : rdn ASEGS mem (Z_to_bv 64 0xff258) 8 = Some (LE8 (Z_to_bv 64 0x1011e8)).
  Hypothesis C_nm : rdn ASEGS mem (Z_to_bv 64 0x1011e8) 8 = Some (LE8 name).

  #[local] Abbreviation M0 := (la_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v).

  Lemma la_msz_facts : (la_msz size mod 4096 = 0 /\ size + 4096 <= la_msz size <= size + 8191)%Z.
  Proof using name rom. (lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end). Z.div_mod_to_equations. lia. Qed.

  Lemma la_pre :
    exists r, msteps ASEGS (mkst regs (0x50554 : word) mem rom) (mkst r (0x82004 : word) M0 rom)
      /\ la_regs sp stats size r /\ getr r 1 = Z_to_bv 64 0x50610 /\ getr r 21 = Z_to_bv 64 8
      /\ getr r 10 = Z_to_bv 64 (la_msz size) /\ getr r 11 = name
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 18; 19; 21; 24]) regs r.
  Proof using C_nm C_gnm C_pg Hstk Hsize Hsp H25 H24 H23 H22 H21 H20 H19 H18 H9 H8 H13 H12 H11 H10 H2 H1.
    (lazymatch goal with |- ?G => let G' := eval unfold la_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. pose proof la_msz_facts as [LF1 LF2].
    wd_eexists. split.
    - an F_5054c D_5054c.                              (* [comment removed for export] *)
      fsd F_50550 D_50550 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_50554 D_50554 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_50558 D_50558 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_5055c D_5055c (at_ sp (-32)).              (* [comment removed for export] *)
      fsd F_50560 D_50560 (at_ sp (-40)).              (* [comment removed for export] *)
      fsd F_50564 D_50564 (at_ sp (-48)).              (* [comment removed for export] *)
      fsd F_50568 D_50568 (at_ sp (-56)).              (* [comment removed for export] *)
      fsd F_5056c D_5056c (at_ sp (-64)).              (* [comment removed for export] *)
      fsd F_50570 D_50570 (at_ sp (-72)).              (* [comment removed for export] *)
      fsd F_50574 D_50574 (at_ sp (-80)).              (* [comment removed for export] *)
      fsd F_50578 D_50578 (at_ sp (-88)).              (* [comment removed for export] *)
      change (wbytes _ _ _) with M0.
      an F_5057c D_5057c.                              (* [comment removed for export] *)
      av F_50580 D_50580 (Z_to_bv 64 7) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av_and F_50584 D_50584 (Z_to_bv 64 0) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      ab_ft F_50588 D_50588 ltac:(condz).              (* [comment removed for export] *)
      an F_5058c D_5058c.                              (* [comment removed for export] *)
      cld8 F_50590 D_50590 (Z_to_bv 64 4096) C_pg.     (* [comment removed for export] *)
      av F_50594 D_50594 (Z_to_bv 64 4095) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av_and F_50598 D_50598 (Z_to_bv 64 0) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      ab_ft F_5059c D_5059c ltac:(condz).              (* [comment removed for export] *)
      an F_505a0 D_505a0.                              (* [comment removed for export] *)
      av F_505a4 D_505a4 (Z_to_bv 64 (size + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      av F_505a8 D_505a8 (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_505ac D_505ac (Z_to_bv 64 (size + 4095)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av_and F_505b0 D_505b0 (Z_to_bv 64 (la_msz size - 4096))
        ltac:(rewrite v_and_m4k; unorm; f_equal; (lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      an F_505b4 D_505b4. try sltu0.                     (* [comment removed for export] *)
      av F_505b8 D_505b8 (Z_to_bv 64 0) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_505bc D_505bc (Z_to_bv 64 (la_msz size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av_and F_505c0 D_505c0 (Z_to_bv 64 0) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_505c4 D_505c4 (Z_to_bv 64 (la_msz size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      ab_tk F_505c8 D_505c8 ltac:(condz).              (* [comment removed for export] *)
      an F_505f0 D_505f0.                              (* [comment removed for export] *)
      an F_505f4 D_505f4.                              (* [comment removed for export] *)
      cld8 F_505f8 D_505f8 (Z_to_bv 64 0x1011e8) C_gnm.   (* [comment removed for export] *)
      cld8 F_505fc D_505fc name C_nm.                  (* [comment removed for export] *)
      an F_50600 D_50600.                              (* [comment removed for export] *)
      an F_50604 D_50604.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End PRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MID.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v stats : word) (size mb : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : la_regs sp stats size regs.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.

  Definition la_post0 (r : bvmap 5 word) : Prop :=
    getr r 10 = Z_to_bv 64 0 /\ getr r 2 = sp /\ getr r 1 = ra
    /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
    /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v
    /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]) regs r.

  (* [comment removed for export] *)
  Section FAIL.
    Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
    Hypothesis S_ra : rdn ASEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
    Hypothesis S_s0 : rdn ASEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
    Hypothesis S_s1 : rdn ASEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
    Hypothesis S_s2 : rdn ASEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
    Hypothesis S_s3 : rdn ASEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).
    Hypothesis S_s4 : rdn ASEGS M (at_ sp (-48)) 8 = Some (LE8 s4v).
    Hypothesis S_s5 : rdn ASEGS M (at_ sp (-56)) 8 = Some (LE8 s5v).
    Hypothesis S_s6 : rdn ASEGS M (at_ sp (-64)) 8 = Some (LE8 s6v).
    Hypothesis S_s7 : rdn ASEGS M (at_ sp (-72)) 8 = Some (LE8 s7v).
    Hypothesis S_s8 : rdn ASEGS M (at_ sp (-80)) 8 = Some (LE8 s8v).
    Hypothesis S_s9 : rdn ASEGS M (at_ sp (-88)) 8 = Some (LE8 s9v).
    Lemma la_fail : exists r, msteps ASEGS (mkst regs (0x50610 : word) M rom) (mkst r ra M rom) /\ la_post0 r.
    Proof using S_s9 S_s8 S_s7 S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra H10 Hret HR size stats.
      destruct HR as (R2 & R8 & R9 & R18 & R19 & R24). (lazymatch goal with |- ?G => let G' := eval unfold la_post0 in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
      wd_eexists. split.
      - ab_tk F_50608 D_50608 ltac:(condz).            (* [comment removed for export] *)
        cld8 F_50828 D_50828 ra S_ra.                  (* [comment removed for export] *)
        cld8 F_5082c D_5082c s0v S_s0. cld8 F_50830 D_50830 s1v S_s1. cld8 F_50834 D_50834 s2v S_s2. cld8 F_50838 D_50838 s3v S_s3.
        cld8 F_5083c D_5083c s4v S_s4. cld8 F_50840 D_50840 s5v S_s5. cld8 F_50844 D_50844 s6v S_s6. cld8 F_50848 D_50848 s7v S_s7.
        cld8 F_5084c D_5084c s8v S_s8. cld8 F_50850 D_50850 s9v S_s9.
        an F_50854 D_50854.                            (* [comment removed for export] *)
        aret F_50858 D_50858 ra.                       (* [comment removed for export] *)
        wd_refl.
      - post. ra_solve.
    Qed.
  End FAIL.

  (* [comment removed for export] *)
  Definition la_regs2 (r : bvmap 5 word) : Prop :=
    la_regs sp stats size r /\ getr r 20 = Z_to_bv 64 mb /\ getr r 22 = Z_to_bv 64 (mb + la_msz size)
    /\ getr r 23 = Z_to_bv 64 (mb + 4096 + size - (mb + 4096 + size) mod 8) /\ getr r 25 = Z_to_bv 64 (mb + 4096)
    /\ getr r 21 = Z_to_bv 64 (mb + 4096 + size).

  Hypothesis Hmb : (4096 <= mb /\ mb + la_msz size < 2 ^ 63 /\ mb mod 4096 = 0)%Z.
  Hypothesis C_pg : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096)).

  Lemma la_mid1 : getr regs 10 = Z_to_bv 64 mb -> getr regs 21 = Z_to_bv 64 8 ->
    exists r, msteps ASEGS (mkst regs (0x50610 : word) M rom) (mkst r (0x6f610 : word) M rom)
      /\ la_regs2 r /\ getr r 1 = Z_to_bv 64 0x50668
      /\ getr r 10 = Z_to_bv 64 mb /\ getr r 11 = Z_to_bv 64 4096 /\ getr r 12 = Z_to_bv 64 250
      /\ regs_agree (fun i : reg => In i [1; 10; 11; 12; 20; 21; 22; 23; 25]) regs r.
  Proof using C_pg Hmb Hsize HR.
    intros H10 H21. destruct HR as (R2 & R8 & R9 & R18 & R19 & R24). (lazymatch goal with |- ?G => let G' := eval unfold la_regs2, la_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    destruct Hmb as (MB1 & MB2 & MB3).
    assert (LF : (la_msz size mod 4096 = 0 /\ size + 4096 <= la_msz size <= size + 8191)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).
    destruct LF as [LF1 LF2].
    assert (RES8 : ((mb + 4096) mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
    wd_eexists. split.
    - ab_ft F_50608 D_50608 ltac:(condz).              (* [comment removed for export] *)
      an F_5060c D_5060c.                              (* [comment removed for export] *)
      cld8 F_50610 D_50610 (Z_to_bv 64 4096) C_pg.     (* [comment removed for export] *)
      av F_50614 D_50614 (Z_to_bv 64 4095) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av_and F_50618 D_50618 (Z_to_bv 64 0) ltac:(apply v_and_4095_al; lia).   (* [comment removed for export] *)
      ab_ft F_5061c D_5061c ltac:(condz).              (* [comment removed for export] *)
      av F_50620 D_50620 (Z_to_bv 64 (mb + la_msz size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_50624 D_50624 (Z_to_bv 64 (mb + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av_and F_50628 D_50628 (Z_to_bv 64 0) ltac:(apply v_and_7_al; lia).   (* [comment removed for export] *)
      an F_5062c D_5062c.                              (* [comment removed for export] *)
      av F_50630 D_50630 (Z_to_bv 64 8) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      an F_50634 D_50634.                              (* [comment removed for export] *)
      an F_50638 D_50638.                              (* [comment removed for export] *)
      av F_5063c D_5063c (Z_to_bv 64 (mb + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_50640 D_50640 (Z_to_bv 64 (mb + 4096 + size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      av F_50644 D_50644 (Z_to_bv 64 (mb + 4096 + 7)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      av F_50648 D_50648 (Z_to_bv 64 (mb + 4096 + size - (mb + 4096 + size) mod 8)) ltac:(apply v_andi_m8; lia).   (* [comment removed for export] *)
      av F_5064c D_5064c (Z_to_bv 64 (mb + 4096)) ltac:(rewrite v_andi_m8 by lia; f_equal; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      av F_50650 D_50650 (Z_to_bv 64 4096) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      an F_50654 D_50654.                              (* [comment removed for export] *)
      an F_50658 D_50658.                              (* [comment removed for export] *)
      an F_5065c D_5065c.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End MID.

(* [comment removed for export] *)
Section MID2.
  Variables (M rom : word -> option byte) (sp stats : word) (size mb : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : la_regs2 sp stats size mb regs.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hmb : (4096 <= mb /\ mb + la_msz size < 2 ^ 63 /\ mb mod 4096 = 0)%Z.
  Lemma la_mid2 :
    exists r, msteps ASEGS (mkst regs (0x50668 : word) M rom) (mkst r (0x6f610 : word) M rom)
      /\ la_regs2 sp stats size mb r /\ getr r 1 = Z_to_bv 64 0x50678
      /\ getr r 10 = Z_to_bv 64 (mb + 4096 + size - (mb + 4096 + size) mod 8)
      /\ getr r 11 = Z_to_bv 64 (mb + la_msz size - (mb + 4096 + size - (mb + 4096 + size) mod 8)) /\ getr r 12 = Z_to_bv 64 250
      /\ regs_agree (fun i : reg => In i [1; 10; 11; 12]) regs r.
  Proof using Hmb Hsize HR.
    destruct HR as ((R2 & R8 & R9 & R18 & R19 & R24) & R20 & R22 & R23 & R25 & R21). (lazymatch goal with |- ?G => let G' := eval unfold la_regs2, la_regs in G in change_no_check G' end).
    destruct Hmb as (MB1 & MB2 & MB3).
    assert (LF : (la_msz size mod 4096 = 0 /\ size + 4096 <= la_msz size <= size + 8191)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).
    destruct LF as [LF1 LF2].
    pose proof (Z.mod_pos_bound (mb + 4096 + size) 8 ltac:(lia)) as MP.
    wd_eexists. split.
    - av F_50660 D_50660 (Z_to_bv 64 (mb + la_msz size - (mb + 4096 + size - (mb + 4096 + size) mod 8)))
        ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; reflexivity).       (* [comment removed for export] *)
      an F_50664 D_50664.                              (* [comment removed for export] *)
      an F_50668 D_50668.                              (* [comment removed for export] *)
      an F_5066c D_5066c.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End MID2.
End FPGen.
End AsAllocM9a.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM9d.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition cbs_m0 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 s3v))
    (at_ sp (-48)) (LE8 s4v).
#[local] Hint Unfold cbs_m0 : asfr.

Section PRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v : word) (size : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f18.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 size.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 8.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (0x10000 < size <= 2 ^ 41)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ sp (-48)) 48 = true.

  Lemma cbs_pre :
    exists r, msteps ASEGS (mkst regs (0x5027c : word) mem rom) (mkst r (0x50554 : word) (cbs_m0 mem sp ra s0v s1v s2v s3v s4v) rom)
      /\ getr r 1 = Z_to_bv 64 0x50324 /\ getr r 2 = at_ sp (-48) /\ getr r 8 = Z_to_bv 64 8
      /\ getr r 10 = Z_to_bv 64 (0x103f18 + 64) /\ getr r 11 = Z_to_bv 64 0x1041c8 /\ getr r 12 = Z_to_bv 64 size /\ getr r 13 = Z_to_bv 64 8
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 10; 11; 12; 14; 15]) regs r.
  Proof using Hstk Hsize Hsp H20 H19 H18 H9 H8 H13 H12 H10 H2 H1.
    pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - an F_50274 D_50274.                              (* [comment removed for export] *)
      fsd F_50278 D_50278 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_5027c D_5027c (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_50280 D_50280 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_50284 D_50284 (at_ sp (-32)).              (* [comment removed for export] *)
      fsd F_50288 D_50288 (at_ sp (-40)).              (* [comment removed for export] *)
      fsd F_5028c D_5028c (at_ sp (-48)).              (* [comment removed for export] *)
      an F_50290 D_50290.                              (* [comment removed for export] *)
      match goal with |- context [v_sltiu ?a ?b] =>
        replace (v_sltiu a b) with (Z_to_bv 64 0)
          by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_sltiu in G in change_no_check G' end); unorm; change (bv_wrap 64 1) with 1%Z; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity) end.
      av F_50294 D_50294 (Z_to_bv 64 size) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_50298 D_50298 (Z_to_bv 64 (2 ^ 64 - 1 - size)) ltac:(apply v_not_lit; lia).   (* [comment removed for export] *)
      ab_tk F_5029c D_5029c ltac:(condz).              (* [comment removed for export] *)
      an F_502c0 D_502c0.                              (* [comment removed for export] *)
      an F_502c4 D_502c4.                              (* [comment removed for export] *)
      ab_tk F_502c8 D_502c8 ltac:(condz).              (* [comment removed for export] *)
      an F_502e8 D_502e8.                              (* [comment removed for export] *)
      ab_ft F_502ec D_502ec ltac:(condz).              (* [comment removed for export] *)
      ab_tk F_502f0 D_502f0 ltac:(condz).              (* [comment removed for export] *)
      av F_50308 D_50308 (Z_to_bv 64 (0x103f18 + 64)) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_5030c D_5030c (Z_to_bv 64 0x1041c8) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      an F_50310 D_50310.                              (* [comment removed for export] *)
      an F_50314 D_50314.                              (* [comment removed for export] *)
      an F_50318 D_50318.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End PRE.

Section RET.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v res : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-48).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 8.
  Hypothesis H10 : getr regs 10 = res.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis S_ra : rdn ASEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn ASEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn ASEGS M (at_ sp (-48)) 8 = Some (LE8 s4v).
  Lemma cbs_ret :
    exists r, msteps ASEGS (mkst regs (0x50324 : word) M rom) (mkst r ra M rom)
      /\ getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 11; 13; 18; 19; 20]) regs r.
  Proof using S_s4 S_s3 S_s2 S_s1 S_s0 S_ra Hret H10 H8 H2.
    pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - an F_5031c D_5031c.                              (* [comment removed for export] *)
      an F_50320 D_50320.                              (* [comment removed for export] *)
      ab_ft F_50324 D_50324 ltac:(condz).              (* [comment removed for export] *)
      an F_50328 D_50328.                              (* [comment removed for export] *)
      cld8 F_50478 D_50478 ra S_ra.                    (* [comment removed for export] *)
      cld8 F_5047c D_5047c s0v S_s0.                   (* [comment removed for export] *)
      cld8 F_50480 D_50480 s1v S_s1.                   (* [comment removed for export] *)
      cld8 F_50484 D_50484 s2v S_s2.                   (* [comment removed for export] *)
      cld8 F_50488 D_50488 s3v S_s3.                   (* [comment removed for export] *)
      cld8 F_5048c D_5048c s4v S_s4.                   (* [comment removed for export] *)
      an F_50490 D_50490.                              (* [comment removed for export] *)
      aret F_50494 D_50494 ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End RET.
End FPGen.
End AsAllocM9d.
Module AsAllocM9m.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition mod_clob : list reg := [1; 2; 8; 9; 18; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

Definition mod_m1 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v size name : word) (PGP : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-36)) (LE4 34))
    (at_ sp (-56)) (LE8 (Z_to_bv 64 0x82070)))
    (at_ sp (-64)) (LE8 name))
    (at_ sp (-72)) (LE8 size))
    (at_ sp (-80)) (LE8 (Z_to_bv 64 PGP)))
    (at_ sp (-88)) (LE8 s3v))
    (at_ sp (-96)) (LE8 s4v))
    (at_ sp (-104)) (LE8 s5v).
#[local] Hint Unfold mod_m1 : asfr.

Section MODPRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v size name : word) (PGP CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = size.
  Hypothesis H11 : getr regs 11 = name.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63)%Z.
  Hypothesis Hname : (U name <> 0)%Z.
  Hypothesis HPGP : (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI)%Z.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ sp (-320)) 320 = true.
  Hypothesis Rgpg : rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn ASEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].

  #[local] Abbreviation M1 := (mod_m1 mem sp ra s0v s1v s2v s3v s4v s5v size name PGP).

  Lemma mod_pre :
    exists r, msteps ASEGS (mkst regs (0x82004 : word) mem rom) (mkst r (0x8073c : word) M1 rom)
      /\ getr r 1 = Z_to_bv 64 0x8208c /\ getr r 2 = at_ sp (-48)
      /\ getr r 8 = name /\ getr r 9 = size /\ getr r 18 = Z_to_bv 64 PGP
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = size /\ getr r 12 = Z_to_bv 64 3 /\ getr r 13 = Z_to_bv 64 34
      /\ getr r 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr r 15 = Z_to_bv 64 0 /\ getr r 17 = Z_to_bv 64 222
      /\ regs_agree (fun i : reg => In i mod_clob) regs r.
  Proof using Rdpm Rgcf Rpg Rgpg Hstk HCF HPGP Hname Hsize Hsp H21 H20 H19 H18 H9 H8 H11 H10 H2 H1 CF.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range size) as Hsr. pose proof (u64_range name) as Hnr.
    destruct Hsize as [Hsz1 Hsz2].
    wd_eexists. split.
    - an F_81ffc D_81ffc.                              (* [comment removed for export] *)
      fsd F_82000 D_82000 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_82004 D_82004 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_82008 D_82008 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_8200c D_8200c (at_ sp (-32)).              (* [comment removed for export] *)
      an F_82010 D_82010.                              (* [comment removed for export] *)
      an F_82014 D_82014.                              (* [comment removed for export] *)
      cld8 F_82018 D_82018 (Z_to_bv 64 PGP) Rgpg.      (* [comment removed for export] *)
      cld8 F_8201c D_8201c (Z_to_bv 64 4096) Rpg.      (* [comment removed for export] *)
      an F_82020 D_82020.                              (* [comment removed for export] *)
      ab_tk F_82024 D_82024 ltac:(condz).              (* [comment removed for export] *)
      an F_82034 D_82034.                              (* [comment removed for export] *)
      an F_82038 D_82038.                              (* [comment removed for export] *)
      ab_ft F_8203c D_8203c ltac:(condz).              (* [comment removed for export] *)
      av F_82040 D_82040 (Z_to_bv 64 (U size + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_82044 D_82044 (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_82048 D_82048 (Z_to_bv 64 (U size + 4095)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av_and F_8204c D_8204c size
        ltac:(rewrite v_and_m4k; unorm; replace (U size + 4095 - (U size + 4095) mod 4096)%Z with (U size) by (Z.div_mod_to_equations; lia); apply Z_to_bv_bv_unsigned).   (* [comment removed for export] *)
      an F_82050 D_82050.                              (* [comment removed for export] *)
      fsw F_82054 D_82054 (at_ sp (-36)).              (* [comment removed for export] *)
      an F_82058 D_82058.                              (* [comment removed for export] *)
      an F_8205c D_8205c.                              (* [comment removed for export] *)
      an F_82060 D_82060.                              (* [comment removed for export] *)
      an F_82064 D_82064.                              (* [comment removed for export] *)
      an F_82adc D_82adc.                              (* [comment removed for export] *)
      fsd F_82ae0 D_82ae0 (at_ sp (-56)).              (* [comment removed for export] *)
      fsd F_82ae4 D_82ae4 (at_ sp (-64)).              (* [comment removed for export] *)
      fsd F_82ae8 D_82ae8 (at_ sp (-72)).              (* [comment removed for export] *)
      fsd F_82aec D_82aec (at_ sp (-80)).              (* [comment removed for export] *)
      fsd F_82af0 D_82af0 (at_ sp (-88)).              (* [comment removed for export] *)
      fsd F_82af4 D_82af4 (at_ sp (-96)).              (* [comment removed for export] *)
      fsd F_82af8 D_82af8 (at_ sp (-104)).             (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
      an F_82afc D_82afc.                              (* [comment removed for export] *)
      an F_82b00 D_82b00.                              (* [comment removed for export] *)
      ab_ft F_82b04 D_82b04 ltac:(condz).              (* [comment removed for export] *)
      an F_82b08 D_82b08.                              (* [comment removed for export] *)
      an F_82b0c D_82b0c.                              (* [comment removed for export] *)
      cld8 F_82b10 D_82b10 (Z_to_bv 64 CF) Rgcf.       (* [comment removed for export] *)
      clbu F_82b14 D_82b14 (Z_to_bv 8 0) Rdpm.         (* [comment removed for export] *)
      an F_82b18 D_82b18.                              (* [comment removed for export] *)
      ab_tk F_82b1c D_82b1c ltac:(condz).              (* [comment removed for export] *)
      an F_82c2c D_82c2c.                              (* [comment removed for export] *)
      fld F_82c30 D_82c30 (Z_to_bv 64 0x82070).        (* [comment removed for export] *)
      fld F_82c34 D_82c34 name.                        (* [comment removed for export] *)
      fld F_82c38 D_82c38 size.                        (* [comment removed for export] *)
      fld F_82c3c D_82c3c (Z_to_bv 64 PGP).            (* [comment removed for export] *)
      fld F_82c40 D_82c40 s3v.                         (* [comment removed for export] *)
      fld F_82c44 D_82c44 s4v.                         (* [comment removed for export] *)
      fld F_82c48 D_82c48 s5v.                         (* [comment removed for export] *)
      an F_82c4c D_82c4c.                              (* [comment removed for export] *)
      rt F_82c50 D_82c50.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 34) (v := Z_to_bv 64 34);
          [exact F_82068 | reflexivity | exact D_82068
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold mod_m1 in G in change_no_check G' end);
            repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]);
            apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
          | reflexivity]
        | step_simpl]; rewrite (v_lw_small 34) by lia; vn.   (* [comment removed for export] *)
      an F_8206c D_8206c.                              (* [comment removed for export] *)
      an F_82070 D_82070.                              (* [comment removed for export] *)
      an F_82074 D_82074.                              (* [comment removed for export] *)
      an F_82078 D_82078.                              (* [comment removed for export] *)
      an F_8207c D_8207c.                              (* [comment removed for export] *)
      an F_82080 D_82080.                              (* [comment removed for export] *)
      an F_80730 D_80730.                              (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold mod_clob in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma mod_m1_outside : forall x : word, (U x < U sp - 320 \/ U sp <= U x)%Z -> M1 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mod_m1 in G in change_no_check G' end).
    repeat (rewrite wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma mod_m1_grows : mem_grows mem M1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mod_m1 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma mod_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v)]%Z -> rdn ASEGS M1 (at_ sp k) 8 = Some (LE8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mod_m1 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
End MODPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MODPOST.
  Variables (M2 rom : word -> option byte) (sp ra s0v s1v s2v size : word) (CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x8208c.
  Hypothesis H2 : getr regs 2 = at_ sp (-48).
  Hypothesis H9 : getr regs 9 = size.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hsok : store_ok ASEGS M2 (at_ sp (-40)) 4 = true.
  Hypothesis S_ra : rdn ASEGS M2 (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS M2 (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS M2 (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS M2 (at_ sp (-32)) 8 = Some (LE8 s2v).

  Ltac mod_epi :=
      an F_820b4 D_820b4;                              (* [comment removed for export] *)
      cld8 F_820b8 D_820b8 ra S_ra;                    (* [comment removed for export] *)
      cld8 F_820bc D_820bc s0v S_s0;                   (* [comment removed for export] *)
      cld8 F_820c0 D_820c0 s1v S_s1;                   (* [comment removed for export] *)
      cld8 F_820c4 D_820c4 s2v S_s2;                   (* [comment removed for export] *)
      an F_820c8 D_820c8;                              (* [comment removed for export] *)
      aret F_820cc D_820cc ra.                         (* [comment removed for export] *)

  Definition mod_ret (r : bvmap 5 word) (res : word) : Prop :=
    getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
    /\ regs_agree (fun i : reg => In i mod_clob) regs r.

  (* [comment removed for export] *)
  Section OK.
    Variable map : word.
    Hypothesis H10 : getr regs 10 = map.
    Hypothesis Hmap : (U map < 2 ^ 63)%Z.
    Hypothesis Rgcf : rdn ASEGS M2 (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)).
    Hypothesis Rlim : rdn ASEGS M2 (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
    Lemma mod_ok :
      exists r, msteps ASEGS (mkst regs (0x80740 : word) M2 rom)
                             (mkst r ra (wbytes M2 (at_ sp (-40)) (LE4 0xffffffffaaaaaaaa)) rom) /\ mod_ret r map.
    Proof using Rlim Rgcf Hmap H10 S_s2 S_s1 S_s0 S_ra Hsok HCF Hret Hsp H9 H2 H1 CF size.
      (lazymatch goal with |- ?G => let G' := eval unfold mod_ret in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. pose proof (u64_range map) as Har.
      wd_eexists. split.
      - rt F_80738 D_80738.                            (* [comment removed for export] *)
        an F_82084 D_82084.                            (* [comment removed for export] *)
        an F_82088 D_82088.                            (* [comment removed for export] *)
        an F_8208c D_8208c.                            (* [comment removed for export] *)
        an F_80710 D_80710.                            (* [comment removed for export] *)
        an F_80714 D_80714.                            (* [comment removed for export] *)
        ab_tk F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
        an F_80728 D_80728. sltu0.                     (* [comment removed for export] *)
        rt F_8072c D_8072c.                            (* [comment removed for export] *)
        an F_82090 D_82090.                            (* [comment removed for export] *)
        an F_82094 D_82094.                            (* [comment removed for export] *)
        fsw F_82098 D_82098 (at_ sp (-40)).            (* [comment removed for export] *)
        an F_8209c D_8209c.                            (* [comment removed for export] *)
        an F_820a0 D_820a0.                            (* [comment removed for export] *)
        an F_820a4 D_820a4.                            (* [comment removed for export] *)
        an F_80710 D_80710.                            (* [comment removed for export] *)
        an F_80714 D_80714.                            (* [comment removed for export] *)
        ab_tk F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
        an F_80728 D_80728. sltu0.                     (* [comment removed for export] *)
        rt F_8072c D_8072c.                            (* [comment removed for export] *)
        ab_ft F_820a8 D_820a8 ltac:(condz).            (* [comment removed for export] *)
        an F_820ac D_820ac.                            (* [comment removed for export] *)
        an F_820b0 D_820b0.                            (* [comment removed for export] *)
        an F_7c614 D_7c614.                            (* [comment removed for export] *)
        cld8 F_7c618 D_7c618 (Z_to_bv 64 CF) Rgcf.     (* [comment removed for export] *)
        cld8 F_7c61c D_7c61c (Z_to_bv 64 0) Rlim.      (* [comment removed for export] *)
        ab_tk F_7c620 D_7c620 ltac:(condz).            (* [comment removed for export] *)
        rt F_7c63c D_7c63c.                            (* [comment removed for export] *)
        mod_epi.
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mod_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End OK.

  (* [comment removed for export] *)
  Section FAIL.
    Hypothesis H10 : getr regs 10 = Z_to_bv 64 (2 ^ 64 - 12).
    Lemma mod_fail :
      exists r, msteps ASEGS (mkst regs (0x80740 : word) M2 rom)
                             (mkst r ra (wbytes (wbytes M2 (at_ sp (-40)) (LE4 0xffffffffaaaaaaaa)) (at_ sp (-40)) (LE4 12)) rom)
        /\ mod_ret r (Z_to_bv 64 0).
    Proof using H10 S_s2 S_s1 S_s0 S_ra Hsok Hret Hsp H2 H1.
      (lazymatch goal with |- ?G => let G' := eval unfold mod_ret in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
      wd_eexists. split.
      - rt F_80738 D_80738.                            (* [comment removed for export] *)
        an F_82084 D_82084.                            (* [comment removed for export] *)
        an F_82088 D_82088.                            (* [comment removed for export] *)
        an F_8208c D_8208c.                            (* [comment removed for export] *)
        an F_80710 D_80710.                            (* [comment removed for export] *)
        an F_80714 D_80714.                            (* [comment removed for export] *)
        ab_ft F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
        ab_tk F_8071c D_8071c ltac:(condz).            (* [comment removed for export] *)
        an F_80728 D_80728.                            (* [comment removed for export] *)
        rt F_8072c D_8072c.                            (* [comment removed for export] *)
        an F_82090 D_82090.                            (* [comment removed for export] *)
        an F_82094 D_82094.                            (* [comment removed for export] *)
        fsw F_82098 D_82098 (at_ sp (-40)).            (* [comment removed for export] *)
        an F_8209c D_8209c.                            (* [comment removed for export] *)
        an F_820a0 D_820a0.                            (* [comment removed for export] *)
        an F_820a4 D_820a4.                            (* [comment removed for export] *)
        an F_80710 D_80710.                            (* [comment removed for export] *)
        an F_80714 D_80714.                            (* [comment removed for export] *)
        ab_ft F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
        ab_ft F_8071c D_8071c ltac:(condz).            (* [comment removed for export] *)
        an F_80720 D_80720.                            (* [comment removed for export] *)
        fsw F_80724 D_80724 (at_ sp (-40)).            (* [comment removed for export] *)
        an F_80728 D_80728.                            (* [comment removed for export] *)
        rt F_8072c D_8072c.                            (* [comment removed for export] *)
        ab_tk F_820a8 D_820a8 ltac:(condz).            (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lw with (bs := LE4 12) (v := Z_to_bv 64 12);
            [exact F_820e0 | reflexivity | exact D_820e0
            | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
              apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
            | reflexivity]
          | step_simpl]; rewrite (v_lw_small 12) by lia; vn.   (* [comment removed for export] *)
        an F_820e4 D_820e4.                            (* [comment removed for export] *)
        ab_ft F_820e8 D_820e8 ltac:(condz).            (* [comment removed for export] *)
        an F_820ec D_820ec.                            (* [comment removed for export] *)
        an F_820f0 D_820f0.                            (* [comment removed for export] *)
        mod_epi.
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mod_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End FAIL.
End MODPOST.
End FPGen.
End AsAllocM9m.
Module AsDepotMnr.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac AsAllocM8m AsAllocM9m OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition mnr_clob : list reg := [1; 2; 8; 9; 18; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

Definition mnr_m1 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v size name : word) (PGP : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-36)) (LE4 16418))
    (at_ sp (-56)) (LE8 (Z_to_bv 64 0x823b0)))
    (at_ sp (-64)) (LE8 name))
    (at_ sp (-72)) (LE8 size))
    (at_ sp (-80)) (LE8 (Z_to_bv 64 PGP)))
    (at_ sp (-88)) (LE8 s3v))
    (at_ sp (-96)) (LE8 s4v))
    (at_ sp (-104)) (LE8 s5v).
#[local] Hint Unfold mnr_m1 : asfr.

Section MODPRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v size name : word) (PGP CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = size.
  Hypothesis H11 : getr regs 11 = name.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63)%Z.
  Hypothesis Hname : (U name <> 0)%Z.
  Hypothesis HPGP : (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI)%Z.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ sp (-320)) 320 = true.
  Hypothesis Rgpg : rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn ASEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].

  #[local] Abbreviation M1 := (mnr_m1 mem sp ra s0v s1v s2v s3v s4v s5v size name PGP).

  Lemma mnr_pre :
    exists r, msteps ASEGS (mkst regs (0x82340 : word) mem rom) (mkst r (0x8073c : word) M1 rom)
      /\ getr r 1 = Z_to_bv 64 0x823cc /\ getr r 2 = at_ sp (-48)
      /\ getr r 8 = name /\ getr r 9 = size /\ getr r 18 = Z_to_bv 64 PGP
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = size /\ getr r 12 = Z_to_bv 64 3 /\ getr r 13 = Z_to_bv 64 16418
      /\ getr r 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr r 15 = Z_to_bv 64 0 /\ getr r 17 = Z_to_bv 64 222
      /\ regs_agree (fun i : reg => In i mnr_clob) regs r.
  Proof using Rdpm Rgcf Rpg Rgpg Hstk HCF HPGP Hname Hsize Hsp H21 H20 H19 H18 H9 H8 H11 H10 H2 H1 CF.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range size) as Hsr. pose proof (u64_range name) as Hnr.
    destruct Hsize as [Hsz1 Hsz2].
    wd_eexists. split.
    - an F_82338 D_82338.                              (* [comment removed for export] *)
      fsd F_8233c D_8233c (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_82340 D_82340 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_82344 D_82344 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_82348 D_82348 (at_ sp (-32)).              (* [comment removed for export] *)
      an F_8234c D_8234c.                              (* [comment removed for export] *)
      an F_82350 D_82350.                              (* [comment removed for export] *)
      cld8 F_82354 D_82354 (Z_to_bv 64 PGP) Rgpg.      (* [comment removed for export] *)
      cld8 F_82358 D_82358 (Z_to_bv 64 4096) Rpg.      (* [comment removed for export] *)
      an F_8235c D_8235c.                              (* [comment removed for export] *)
      ab_tk F_82360 D_82360 ltac:(condz).              (* [comment removed for export] *)
      an F_82370 D_82370.                              (* [comment removed for export] *)
      an F_82374 D_82374.                              (* [comment removed for export] *)
      ab_ft F_82378 D_82378 ltac:(condz).              (* [comment removed for export] *)
      av F_8237c D_8237c (Z_to_bv 64 (U size + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_82380 D_82380 (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_82384 D_82384 (Z_to_bv 64 (U size + 4095)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av_and F_82388 D_82388 size
        ltac:(rewrite v_and_m4k; unorm; replace (U size + 4095 - (U size + 4095) mod 4096)%Z with (U size) by (Z.div_mod_to_equations; lia); apply Z_to_bv_bv_unsigned).   (* [comment removed for export] *)
      an F_8238c D_8238c.                              (* [comment removed for export] *)
      av F_82390 D_82390 (Z_to_bv 64 16418) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      fsw F_82394 D_82394 (at_ sp (-36)).              (* [comment removed for export] *)
      an F_82398 D_82398.                              (* [comment removed for export] *)
      an F_8239c D_8239c.                              (* [comment removed for export] *)
      an F_823a0 D_823a0.                              (* [comment removed for export] *)
      an F_823a4 D_823a4.                              (* [comment removed for export] *)
      an F_82adc D_82adc.                              (* [comment removed for export] *)
      fsd F_82ae0 D_82ae0 (at_ sp (-56)).              (* [comment removed for export] *)
      fsd F_82ae4 D_82ae4 (at_ sp (-64)).              (* [comment removed for export] *)
      fsd F_82ae8 D_82ae8 (at_ sp (-72)).              (* [comment removed for export] *)
      fsd F_82aec D_82aec (at_ sp (-80)).              (* [comment removed for export] *)
      fsd F_82af0 D_82af0 (at_ sp (-88)).              (* [comment removed for export] *)
      fsd F_82af4 D_82af4 (at_ sp (-96)).              (* [comment removed for export] *)
      fsd F_82af8 D_82af8 (at_ sp (-104)).             (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
      an F_82afc D_82afc.                              (* [comment removed for export] *)
      an F_82b00 D_82b00.                              (* [comment removed for export] *)
      ab_ft F_82b04 D_82b04 ltac:(condz).              (* [comment removed for export] *)
      an F_82b08 D_82b08.                              (* [comment removed for export] *)
      an F_82b0c D_82b0c.                              (* [comment removed for export] *)
      cld8 F_82b10 D_82b10 (Z_to_bv 64 CF) Rgcf.       (* [comment removed for export] *)
      clbu F_82b14 D_82b14 (Z_to_bv 8 0) Rdpm.         (* [comment removed for export] *)
      an F_82b18 D_82b18.                              (* [comment removed for export] *)
      ab_tk F_82b1c D_82b1c ltac:(condz).              (* [comment removed for export] *)
      an F_82c2c D_82c2c.                              (* [comment removed for export] *)
      fld F_82c30 D_82c30 (Z_to_bv 64 0x823b0).        (* [comment removed for export] *)
      fld F_82c34 D_82c34 name.                        (* [comment removed for export] *)
      fld F_82c38 D_82c38 size.                        (* [comment removed for export] *)
      fld F_82c3c D_82c3c (Z_to_bv 64 PGP).            (* [comment removed for export] *)
      fld F_82c40 D_82c40 s3v.                         (* [comment removed for export] *)
      fld F_82c44 D_82c44 s4v.                         (* [comment removed for export] *)
      fld F_82c48 D_82c48 s5v.                         (* [comment removed for export] *)
      an F_82c4c D_82c4c.                              (* [comment removed for export] *)
      rt F_82c50 D_82c50.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 16418) (v := Z_to_bv 64 16418);
          [exact F_823a8 | reflexivity | exact D_823a8
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold mnr_m1 in G in change_no_check G' end);
            repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]);
            apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
          | reflexivity]
        | step_simpl]; rewrite (v_lw_small 16418) by lia; vn.   (* [comment removed for export] *)
      an F_823ac D_823ac.                              (* [comment removed for export] *)
      an F_823b0 D_823b0.                              (* [comment removed for export] *)
      an F_823b4 D_823b4.                              (* [comment removed for export] *)
      an F_823b8 D_823b8.                              (* [comment removed for export] *)
      an F_823bc D_823bc.                              (* [comment removed for export] *)
      an F_823c0 D_823c0.                              (* [comment removed for export] *)
      an F_80730 D_80730.                              (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold mnr_clob in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma mnr_m1_outside : forall x : word, (U x < U sp - 320 \/ U sp <= U x)%Z -> M1 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mnr_m1 in G in change_no_check G' end).
    repeat (rewrite wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma mnr_m1_grows : mem_grows mem M1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mnr_m1 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma mnr_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v)]%Z -> rdn ASEGS M1 (at_ sp k) 8 = Some (LE8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mnr_m1 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
End MODPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MODPOST.
  Variables (M2 rom : word -> option byte) (sp ra s0v s1v s2v size : word) (CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x823cc.
  Hypothesis H2 : getr regs 2 = at_ sp (-48).
  Hypothesis H9 : getr regs 9 = size.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hsok : store_ok ASEGS M2 (at_ sp (-40)) 4 = true.
  Hypothesis S_ra : rdn ASEGS M2 (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS M2 (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS M2 (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS M2 (at_ sp (-32)) 8 = Some (LE8 s2v).

  Ltac mnr_epi :=
      an F_823f4 D_823f4;                              (* [comment removed for export] *)
      cld8 F_823f8 D_823f8 ra S_ra;                    (* [comment removed for export] *)
      cld8 F_823fc D_823fc s0v S_s0;                   (* [comment removed for export] *)
      cld8 F_82400 D_82400 s1v S_s1;                   (* [comment removed for export] *)
      cld8 F_82404 D_82404 s2v S_s2;                   (* [comment removed for export] *)
      an F_82408 D_82408;                              (* [comment removed for export] *)
      aret F_8240c D_8240c ra.                         (* [comment removed for export] *)

  Definition mnr_ret (r : bvmap 5 word) (res : word) : Prop :=
    getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
    /\ regs_agree (fun i : reg => In i mnr_clob) regs r.

  (* [comment removed for export] *)
  Section OK.
    Variable map : word.
    Hypothesis H10 : getr regs 10 = map.
    Hypothesis Hmap : (U map < 2 ^ 63)%Z.
    Hypothesis Rgcf : rdn ASEGS M2 (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)).
    Hypothesis Rlim : rdn ASEGS M2 (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
    Lemma mnr_ok :
      exists r, msteps ASEGS (mkst regs (0x80740 : word) M2 rom)
                             (mkst r ra (wbytes M2 (at_ sp (-40)) (LE4 0xffffffffaaaaaaaa)) rom) /\ mnr_ret r map.
    Proof using Rlim Rgcf Hmap H10 S_s2 S_s1 S_s0 S_ra Hsok HCF Hret Hsp H9 H2 H1 CF size.
      (lazymatch goal with |- ?G => let G' := eval unfold mnr_ret in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. pose proof (u64_range map) as Har.
      wd_eexists. split.
      - rt F_80738 D_80738.                            (* [comment removed for export] *)
        an F_823c4 D_823c4.                            (* [comment removed for export] *)
        an F_823c8 D_823c8.                            (* [comment removed for export] *)
        an F_823cc D_823cc.                            (* [comment removed for export] *)
        an F_80710 D_80710.                            (* [comment removed for export] *)
        an F_80714 D_80714.                            (* [comment removed for export] *)
        ab_tk F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
        an F_80728 D_80728. sltu0.                     (* [comment removed for export] *)
        rt F_8072c D_8072c.                            (* [comment removed for export] *)
        an F_823d0 D_823d0.                            (* [comment removed for export] *)
        an F_823d4 D_823d4.                            (* [comment removed for export] *)
        fsw F_823d8 D_823d8 (at_ sp (-40)).            (* [comment removed for export] *)
        an F_823dc D_823dc.                            (* [comment removed for export] *)
        an F_823e0 D_823e0.                            (* [comment removed for export] *)
        an F_823e4 D_823e4.                            (* [comment removed for export] *)
        an F_80710 D_80710.                            (* [comment removed for export] *)
        an F_80714 D_80714.                            (* [comment removed for export] *)
        ab_tk F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
        an F_80728 D_80728. sltu0.                     (* [comment removed for export] *)
        rt F_8072c D_8072c.                            (* [comment removed for export] *)
        ab_ft F_823e8 D_823e8 ltac:(condz).            (* [comment removed for export] *)
        an F_823ec D_823ec.                            (* [comment removed for export] *)
        an F_823f0 D_823f0.                            (* [comment removed for export] *)
        an F_7c614 D_7c614.                            (* [comment removed for export] *)
        cld8 F_7c618 D_7c618 (Z_to_bv 64 CF) Rgcf.     (* [comment removed for export] *)
        cld8 F_7c61c D_7c61c (Z_to_bv 64 0) Rlim.      (* [comment removed for export] *)
        ab_tk F_7c620 D_7c620 ltac:(condz).            (* [comment removed for export] *)
        rt F_7c63c D_7c63c.                            (* [comment removed for export] *)
        mnr_epi.
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mnr_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End OK.

  (* [comment removed for export] *)
  Section DIE.
    Hypothesis H10 : getr regs 10 = Z_to_bv 64 (2 ^ 64 - 12).
    Hypothesis Hstk2 : store_ok ASEGS M2 (at_ sp (-96)) 48 = true.
    Hypothesis Rdie1 : rdn ASEGS M2 (Z_to_bv 64 0xff2b0) 8 = Some (LE8 (Z_to_bv 64 1)).
    Hypothesis Rdie2 : rdn ASEGS M2 (Z_to_bv 64 0x19909c) 4 = Some (LE4 0).
    Lemma mnr_die :
      exists r M', msteps ASEGS (mkst regs (0x80740 : word) M2 rom) (mkst r (0x7bfb4 : word) M' rom).
    Proof using Rdie2 Rdie1 Hstk2 H10 Hsok Hsp H9 H2 H1 size sp.
      pose proof (u64_range sp) as Hspr.
      wd_eexists. wd_eexists.
      rt F_80738 D_80738.                            (* [comment removed for export] *)
      an F_823c4 D_823c4.                            (* [comment removed for export] *)
      an F_823c8 D_823c8.                            (* [comment removed for export] *)
      an F_823cc D_823cc.                            (* [comment removed for export] *)
      an F_80710 D_80710.                            (* [comment removed for export] *)
      an F_80714 D_80714.                            (* [comment removed for export] *)
      ab_ft F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
      ab_tk F_8071c D_8071c ltac:(condz).            (* [comment removed for export] *)
      an F_80728 D_80728.                            (* [comment removed for export] *)
      rt F_8072c D_8072c.                            (* [comment removed for export] *)
      an F_823d0 D_823d0.                            (* [comment removed for export] *)
      an F_823d4 D_823d4.                            (* [comment removed for export] *)
      fsw F_823d8 D_823d8 (at_ sp (-40)).            (* [comment removed for export] *)
      an F_823dc D_823dc.                            (* [comment removed for export] *)
      an F_823e0 D_823e0.                            (* [comment removed for export] *)
      an F_823e4 D_823e4.                            (* [comment removed for export] *)
      an F_80710 D_80710.                            (* [comment removed for export] *)
      an F_80714 D_80714.                            (* [comment removed for export] *)
      ab_ft F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
      ab_ft F_8071c D_8071c ltac:(condz).            (* [comment removed for export] *)
      an F_80720 D_80720.                            (* [comment removed for export] *)
      fsw F_80724 D_80724 (at_ sp (-40)).            (* [comment removed for export] *)
      an F_80728 D_80728.                            (* [comment removed for export] *)
      rt F_8072c D_8072c.                            (* [comment removed for export] *)
      ab_tk F_823e8 D_823e8 ltac:(condz).            (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 12) (v := Z_to_bv 64 12);
          [exact F_82420 | reflexivity | exact D_82420
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
            apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
          | reflexivity]
        | step_simpl]; rewrite (v_lw_small 12) by lia; vn.   (* [comment removed for export] *)
      an F_82424 D_82424.                            (* [comment removed for export] *)
      an F_82428 D_82428.                            (* [comment removed for export] *)
      an F_8242c D_8242c.                            (* [comment removed for export] *)
      an F_82430 D_82430.                            (* [comment removed for export] *)
      an F_82434 D_82434.                            (* [comment removed for export] *)
      an F_82438 D_82438.                            (* [comment removed for export] *)
      an F_7bf7c D_7bf7c.                            (* [comment removed for export] *)
      fsd F_7bf80 D_7bf80 (at_ sp (-56)).            (* [comment removed for export] *)
      fsd F_7bf84 D_7bf84 (at_ sp (-64)).            (* [comment removed for export] *)
      fsd F_7bf88 D_7bf88 (at_ sp (-72)).            (* [comment removed for export] *)
      fsd F_7bf8c D_7bf8c (at_ sp (-80)).            (* [comment removed for export] *)
      fsd F_7bf90 D_7bf90 (at_ sp (-88)).            (* [comment removed for export] *)
      an F_7bf94 D_7bf94.                            (* [comment removed for export] *)
      cld8 F_7bf98 D_7bf98 (Z_to_bv 64 1) Rdie1.     (* [comment removed for export] *)
      ab_ft F_7bf9c D_7bf9c ltac:(condz).            (* [comment removed for export] *)
      an F_7bfa0 D_7bfa0.                            (* [comment removed for export] *)
      clw F_7bfa4 D_7bfa4 (LE4 0) (Z_to_bv 64 0) Rdie2 (eq_refl : bytes_le_to_Z (LE4 0) = U (Z_to_bv 64 0)).   (* [comment removed for export] *)
      try (rewrite (v_lw_small 0) by lia).
      ab_ft F_7bfa8 D_7bfa8 ltac:(condz).            (* [comment removed for export] *)
      wd_refl.
    Qed.

  End DIE.
End MODPOST.
End FPGen.
End AsDepotMnr.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a.AsAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF7 AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p AsAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.
Ltac pc4 := apply bv_eq; reflexivity.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition la_m1 (M : word -> option byte) (thr v72 v80 : word) (size mb : Z) (b1 b2 b3 : byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
    (at_ thr 2872) (LE8 (v_addi v72 1)))
    (at_ thr 2880) (LE8 (v_add v80 (Z_to_bv 64 (la_msz size)))))
    (Z_to_bv 64 mb) (LE8 (Z_to_bv 64 mb)))
    (Z_to_bv 64 (mb + 8)) (LE8 (Z_to_bv 64 (la_msz size))))
    (Z_to_bv 64 (mb + 16)) (LE8 (Z_to_bv 64 size)))
    (Z_to_bv 64 0x1041c0) [Z_to_bv 8 1; b1; b2; b3].
#[local] Hint Unfold la_m1 : asfr.

Section T1.
  Variables (M rom : word -> option byte) (sp stats thr v72 v80 lkw : word) (size mb T : Z) (b1 b2 b3 : byte).
  Variable regs : bvmap 5 word.
  Hypothesis HR : la_regs2 sp stats size mb regs.
  Hypothesis H10 : getr regs 10 = at_ thr 2800.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hmb : (AIMGHI <= mb /\ mb + la_msz size < 2 ^ 63 /\ mb mod 4096 = 0)%Z.
  Hypothesis HT : (U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 96 /\ T mod 8 = 0)%Z.
  Hypothesis HTmb : (T + 4096 <= mb \/ mb + la_msz size <= T)%Z.
  Hypothesis Hmbsp : (mb + la_msz size <= U sp - 96 \/ U sp <= mb)%Z.
  Hypothesis HTimg : (T + 4096 <= AIMGLO \/ AIMGHI <= T)%Z.
  Hypothesis R_72 : rdn ASEGS M (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R_80 : rdn ASEGS M (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis C_pg : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis R_lock : rdn ASEGS M (Z_to_bv 64 0x1041c0) 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis V_lock : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U lkw.
  Hypothesis SOK_T : store_ok ASEGS M thr 4096 = true.
  Hypothesis SOK_h : store_ok ASEGS M (Z_to_bv 64 mb) 32 = true.
  Hypothesis SOK_lk : store_ok ASEGS M (Z_to_bv 64 0x1041c0) 4 = true.

  Lemma la_t1 :
    exists r, msteps ASEGS (mkst regs (0x5067c : word) M rom) (mkst r (0x50700 : word) (la_m1 M thr v72 v80 size mb b1 b2 b3) rom)
      /\ la_regs sp stats size r /\ getr r 21 = Z_to_bv 64 mb /\ getr r 10 = Z_to_bv 64 (mb + 4096)
      /\ regs_agree (fun i : reg => In i [10; 11; 12; 13; 14; 15; 16; 21]) regs r.
  Proof using SOK_lk SOK_h SOK_T V_lock R_lock C_pg R_80 R_72 HTimg HT Hmb Hsize Hsp H10 HR T lkw. clear - SOK_lk SOK_h SOK_T V_lock R_lock C_pg R_80 R_72 HTimg HT Hmb Hsize Hsp H10 HR T lkw.
    destruct HR as ((R2 & R8 & R9 & R18 & R19 & R24) & R20 & R22 & R23 & R25 & R21). (lazymatch goal with |- ?G => let G' := eval unfold la_regs in G in change_no_check G' end).
    destruct Hmb as (MB1 & MB2 & MB3). destruct HT as (UT & T1 & T2 & T3). pose proof (u64_range sp) as Hspr.
    assert (LF : (la_msz size mod 4096 = 0 /\ size + 4096 <= la_msz size <= size + 8191)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).
    destruct LF as [LF1 LF2].
    pose proof (Z.mod_pos_bound (mb + 4096 + size) 8 ltac:(lia)) as MP.
    wd_eexists. split.
    - cld8 F_50674 D_50674 v72 R_72.                   (* [comment removed for export] *)
      cld8 F_50678 D_50678 v80 R_80.                   (* [comment removed for export] *)
      av_and F_5067c D_5067c (Z_to_bv 64 0) ltac:(apply v_and_7_al; [lia | Z.div_mod_to_equations; lia]).   (* [comment removed for export] *)
      an F_50680 D_50680.                              (* [comment removed for export] *)
      an F_50684 D_50684.                              (* [comment removed for export] *)
      fsd F_50688 D_50688 (at_ thr 2872).              (* [comment removed for export] *)
      fsd F_5068c D_5068c (at_ thr 2880).              (* [comment removed for export] *)
      ab_ft F_50690 D_50690 ltac:(condz).              (* [comment removed for export] *)
      an F_50694 D_50694.                              (* [comment removed for export] *)
      cld8 F_50698 D_50698 (Z_to_bv 64 4096) C_pg.     (* [comment removed for export] *)
      av F_5069c D_5069c (Z_to_bv 64 4095) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av_and F_506a0 D_506a0 (Z_to_bv 64 0) ltac:(apply v_and_4095_al; [lia | Z.div_mod_to_equations; lia]).   (* [comment removed for export] *)
      ab_ft F_506a4 D_506a4 ltac:(condz).              (* [comment removed for export] *)
      ab_ft F_506a8 D_506a8 ltac:(condz).              (* [comment removed for export] *)
      ab_ft F_506ac D_506ac ltac:(condz).              (* [comment removed for export] *)
      av F_506b0 D_506b0 (Z_to_bv 64 mb) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      fsd F_506b4 D_506b4 (Z_to_bv 64 mb).             (* [comment removed for export] *)
      fsd F_506b8 D_506b8 (Z_to_bv 64 (mb + 8)).       (* [comment removed for export] *)
      fsd F_506bc D_506bc (Z_to_bv 64 (mb + 16)).      (* [comment removed for export] *)
      ab_ft F_506c0 D_506c0 ltac:(condz).              (* [comment removed for export] *)
      av F_506c4 D_506c4 (Z_to_bv 64 0x1041c0) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      an F_506c8 D_506c8.                              (* [comment removed for export] *)
      av F_506cc D_506cc (Z_to_bv 64 0x1041c0) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      an F_506d0 D_506d0.                              (* [comment removed for export] *)
      (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (xchg_byte_run ASEGS _ (0x506dc : word) (0x506e0 : word) (0x506e4 : word) (0x506e8 : word)
                  (0x506ec : word) (0x506f0 : word) (0x506f4 : word) (0x506f8 : word) _ rom
                  _ _ _ _ _ _ _ _ _ _ _ 15 13 16 14 12 _ [Z_to_bv 8 0; b1; b2; b3] lkw 0%nat 1%Z
                  F_506d4 eq_refl D_506d4 F_506d8 eq_refl D_506d8 F_506dc eq_refl D_506dc F_506e0 eq_refl D_506e0
                  F_506e4 eq_refl D_506e4 F_506e8 eq_refl D_506e8 F_506ec eq_refl D_506ec).
        all: lazymatch goal with
             | |- v_addi _ _ = _ => first [reflexivity | apply bv_eq; vm_compute; reflexivity]
             | |- _ <> _ => first [regneq | intros X; discriminate X]
             | |- (_ mod 4 = 0)%Z => gres; rwH; unorm; reflexivity
             | |- rdn _ _ _ _ = _ => gres; rwH; rd_peel; exact R_lock
             | |- bytes_le_to_Z _ = _ => exact V_lock
             | |- store_ok _ _ _ _ = true => gres; rwH; any_ok
             | |- (_ < _)%nat => lia
             | |- (_ <= _ < _)%Z => lia
             | |- U _ = _ => gres; rwH; unorm; reflexivity
             end. }
      gres. rwH. (lazymatch goal with |- ?G => let G' := eval cbn [firstn skipn app] in G in change_no_check G' end).
      av F_506f0 D_506f0 (Z_to_bv 64 0) ltac:(rewrite (lock_byte0 (Z_to_bv 8 0) b1 b2 b3 _ V_lock); unorm; reflexivity).   (* [comment removed for export] *)
      ab_ft F_506f4 D_506f4 ltac:(condz).              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End T1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section T2.
  Variables (M rom : word -> option byte) (sp stats : word) (size mb nch nres PA cz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : la_regs sp stats size regs.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 mb.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hnch : (0 <= nch < 2 ^ 20 /\ nch <> nres /\ 0 <= nres < 2 ^ 64)%Z.
  Hypothesis Hclz : (U (swar_clz (Z_to_bv 64 (la_msz size))) = cz /\ 0 <= cz <= 63)%Z.
  Hypothesis R_nch : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 120)) 8 = Some (LE8 (Z_to_bv 64 nch)).
  Hypothesis R_nres : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).

End T2.

(* [comment removed for export] *)
Section T2P.
  Variables (M rom : word -> option byte) (smw : word) (nres : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (0x103f18 + 64).
  Hypothesis H11 : getr regs 11 = smw.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 0x5555555555555555.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 0x3333333333333333.
  Hypothesis H15 : getr regs 15 = Z_to_bv 64 0x0f0f0f0f0f0f0f0f.
  Hypothesis R_nres : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).

End T2P.

Section T2C.
  Variables (M rom : word -> option byte) (sp stats : word) (size mb nch nres PA cz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : la_regs sp stats size regs.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 mb.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hnch : (0 <= nch < 2 ^ 20 /\ nch <> nres /\ 0 <= nres < 2 ^ 64)%Z.
  Hypothesis Hclz : (U (swar_clz (Z_to_bv 64 (la_msz size))) = cz /\ 0 <= cz <= 63)%Z.
  Hypothesis R_nch : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 120)) 8 = Some (LE8 (Z_to_bv 64 nch)).
  Hypothesis R_nres : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).


End T2C.
End FPGen.
