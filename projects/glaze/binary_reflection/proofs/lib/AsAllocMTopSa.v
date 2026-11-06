(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module AsAllocM9h.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
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
Definition mfo_m0 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 s3v))
    (at_ sp (-48)) (LE8 s4v).
Definition mfo_m1 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v addr size name : word) (PGP : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (mfo_m0 mem sp ra s0v s1v s2v s3v s4v)
    (at_ sp (-96)) (LE4 50))
    (at_ sp (-104)) (LE8 (Z_to_bv 64 0x824e0)))
    (at_ sp (-112)) (LE8 size))
    (at_ sp (-120)) (LE8 (Z_to_bv 64 0)))
    (at_ sp (-128)) (LE8 addr))
    (at_ sp (-136)) (LE8 name))
    (at_ sp (-144)) (LE8 (Z_to_bv 64 PGP)))
    (at_ sp (-152)) (LE8 s5v).
#[local] Hint Unfold mfo_m0 mfo_m1 : asfr.

Section MFOPRE.
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
  Hypothesis Hname : (U name = 0)%Z.
  Hypothesis HPGP : (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI)%Z.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ sp (-368)) 368 = true.
  Hypothesis Rgpg : rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).

  #[local] Abbreviation M1 := (mfo_m1 mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP).

  Lemma mfo_pre :
    exists r, msteps ASEGS (mkst regs (0x8a7d4 : word) mem rom) (mkst r (0x8073c : word) M1 rom)
      /\ getr r 1 = Z_to_bv 64 0x824fc /\ getr r 2 = at_ sp (-96)
      /\ getr r 8 = size /\ getr r 9 = Z_to_bv 64 0 /\ getr r 18 = addr /\ getr r 19 = name /\ getr r 20 = Z_to_bv 64 PGP
      /\ getr r 10 = addr /\ getr r 11 = size /\ getr r 12 = Z_to_bv 64 3 /\ getr r 13 = Z_to_bv 64 50
      /\ getr r 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr r 15 = Z_to_bv 64 0 /\ getr r 17 = Z_to_bv 64 222
      /\ regs_agree (fun i : reg => In i (1%bv :: 2%bv :: 8%bv :: 9%bv :: 18%bv :: 19%bv :: 20%bv :: mfi_clob)) regs r.
  Proof using Rpg Rgpg Hstk HPGP Hname Hsize Haddr Hsp H21 H20 H19 H18 H9 H8 H13 H12 H11 H2 H1.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range addr) as Har. pose proof (u64_range size) as Hsr. pose proof (u64_range name) as Hnr.
    destruct Hsize as [Hsz1 Hsz2].
    wd_eexists. split.
    - an F_8a7cc D_8a7cc.                              (* [comment removed for export] *)
      an F_8a7d0 D_8a7d0.                              (* [comment removed for export] *)
      an F_8a7d4 D_8a7d4.                              (* [comment removed for export] *)
      an F_8a7d8 D_8a7d8.                              (* [comment removed for export] *)
      an F_8243c D_8243c.                              (* [comment removed for export] *)
      an F_82440 D_82440.                              (* [comment removed for export] *)
      an F_82444 D_82444.                              (* [comment removed for export] *)
      an F_82448 D_82448.                              (* [comment removed for export] *)
      fsd F_8244c D_8244c (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_82450 D_82450 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_82454 D_82454 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_82458 D_82458 (at_ sp (-32)).              (* [comment removed for export] *)
      fsd F_8245c D_8245c (at_ sp (-40)).              (* [comment removed for export] *)
      fsd F_82460 D_82460 (at_ sp (-48)).              (* [comment removed for export] *)
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
      fsw F_824c4 D_824c4 (at_ sp (-96)).              (* [comment removed for export] *)
      an F_824c8 D_824c8.                              (* [comment removed for export] *)
      an F_824cc D_824cc.                              (* [comment removed for export] *)
      an F_824d0 D_824d0.                              (* [comment removed for export] *)
      an F_824d4 D_824d4.                              (* [comment removed for export] *)
      an F_82adc D_82adc.                              (* [comment removed for export] *)
      fsd F_82ae0 D_82ae0 (at_ sp (-104)).             (* [comment removed for export] *)
      fsd F_82ae4 D_82ae4 (at_ sp (-112)).             (* [comment removed for export] *)
      fsd F_82ae8 D_82ae8 (at_ sp (-120)).             (* [comment removed for export] *)
      fsd F_82aec D_82aec (at_ sp (-128)).             (* [comment removed for export] *)
      fsd F_82af0 D_82af0 (at_ sp (-136)).             (* [comment removed for export] *)
      fsd F_82af4 D_82af4 (at_ sp (-144)).             (* [comment removed for export] *)
      fsd F_82af8 D_82af8 (at_ sp (-152)).             (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
      an F_82afc D_82afc.                              (* [comment removed for export] *)
      an F_82b00 D_82b00.                              (* [comment removed for export] *)
      ab_tk F_82b04 D_82b04 ltac:(condz).              (* [comment removed for export] *)
      an F_82c2c D_82c2c.                              (* [comment removed for export] *)
      fld F_82c30 D_82c30 (Z_to_bv 64 0x824e0).        (* [comment removed for export] *)
      fld F_82c34 D_82c34 size.                        (* [comment removed for export] *)
      fld F_82c38 D_82c38 (Z_to_bv 64 0).              (* [comment removed for export] *)
      fld F_82c3c D_82c3c addr.                        (* [comment removed for export] *)
      fld F_82c40 D_82c40 name.                        (* [comment removed for export] *)
      fld F_82c44 D_82c44 (Z_to_bv 64 PGP).            (* [comment removed for export] *)
      fld F_82c48 D_82c48 s5v.                         (* [comment removed for export] *)
      an F_82c4c D_82c4c.                              (* [comment removed for export] *)
      rt F_82c50 D_82c50.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 50) (v := Z_to_bv 64 50);
          [exact F_824d8 | reflexivity | exact D_824d8
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold mfo_m1 in G in change_no_check G' end);
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
  Lemma mfo_m1_outside : forall x : word, (U x < U sp - 368 \/ U sp <= U x)%Z -> M1 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mfo_m1, mfo_m0 in G in change_no_check G' end).
    repeat (rewrite wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma mfo_m1_grows : mem_grows mem M1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mfo_m1, mfo_m0 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma mfo_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v)]%Z -> rdn ASEGS M1 (at_ sp k) 8 = Some (LE8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mfo_m1, mfo_m0 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
End MFOPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MFOPOST.
  Variables (M2 rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v addr size name : word) (PGP CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x824fc.
  Hypothesis H2 : getr regs 2 = at_ sp (-96).
  Hypothesis H8 : getr regs 8 = size.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 0.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hsok : store_ok ASEGS M2 (at_ sp (-52)) 4 = true.
  Hypothesis S_ra : rdn ASEGS M2 (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS M2 (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS M2 (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS M2 (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn ASEGS M2 (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn ASEGS M2 (at_ sp (-48)) 8 = Some (LE8 s4v).

  
  (* [comment removed for export] *)
  Section OK.
    Hypothesis H10 : getr regs 10 = addr.
    Hypothesis Haddr : (U addr < 2 ^ 63)%Z.
    Hypothesis Rgcf : rdn ASEGS M2 (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)).
    Hypothesis Rlim : rdn ASEGS M2 (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
    Lemma mfo_ok :
      exists r, msteps ASEGS (mkst regs (0x80740 : word) M2 rom)
                             (mkst r ra (wbytes M2 (at_ sp (-52)) (LE4 0xffffffffaaaaaaaa)) rom)
        /\ getr r 10 = addr /\ getr r 2 = sp /\ getr r 1 = ra
        /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
        /\ regs_agree (fun i : reg => In i mfi_clob2) regs r.
    Proof using Rlim Rgcf Haddr H10 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra Hsok HCF Hret Hsp H8 H2 H1 CF size.
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
        fsw F_82508 D_82508 (at_ sp (-52)).            (* [comment removed for export] *)
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
        cld8 F_82528 D_82528 ra S_ra.                  (* [comment removed for export] *)
        cld8 F_8252c D_8252c s0v S_s0.                 (* [comment removed for export] *)
        cld8 F_82530 D_82530 s1v S_s1.                 (* [comment removed for export] *)
        cld8 F_82534 D_82534 s2v S_s2.                 (* [comment removed for export] *)
        cld8 F_82538 D_82538 s3v S_s3.                 (* [comment removed for export] *)
        cld8 F_8253c D_8253c s4v S_s4.                 (* [comment removed for export] *)
        an F_82540 D_82540.                            (* [comment removed for export] *)
        aret F_82544 D_82544 ra.                       (* [comment removed for export] *)
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End OK.

  (* [comment removed for export] *)
  Section FAIL.
    Hypothesis H10 : getr regs 10 = Z_to_bv 64 (2 ^ 64 - 12).
    Lemma mfo_fail :
      exists r, msteps ASEGS (mkst regs (0x80740 : word) M2 rom)
                             (mkst r (0x82578 : word) (wbytes (wbytes M2 (at_ sp (-52)) (LE4 0xffffffffaaaaaaaa)) (at_ sp (-52)) (LE4 12)) rom)
        /\ getr r 2 = at_ sp (-96) /\ getr r 8 = size /\ getr r 9 = Z_to_bv 64 0 /\ getr r 19 = Z_to_bv 64 (2 ^ 64 - 12)
        /\ getr r 18 = getr regs 18 /\ getr r 20 = getr regs 20
        /\ regs_agree (fun i : reg => In i (19%bv :: mfi_clob2)) regs r.
    Proof using H10 Hsok Hsp H9 H8 H2 H1.
      pose proof (u64_range sp) as Hspr.
      wd_eexists. split.
      - rt F_80738 D_80738.                            (* [comment removed for export] *)
        an F_824f4 D_824f4.                            (* [comment removed for export] *)
        an F_824f8 D_824f8.                            (* [comment removed for export] *)
        an F_824fc D_824fc.                            (* [comment removed for export] *)
        an F_80710 D_80710.                            (* [comment removed for export] *)
        an F_80714 D_80714.                            (* [comment removed for export] *)
        ab_ft F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
        ab_tk F_8071c D_8071c ltac:(condz).            (* [comment removed for export] *)
        an F_80728 D_80728.                            (* [comment removed for export] *)
        rt F_8072c D_8072c.                            (* [comment removed for export] *)
        an F_82500 D_82500.                            (* [comment removed for export] *)
        an F_82504 D_82504.                            (* [comment removed for export] *)
        fsw F_82508 D_82508 (at_ sp (-52)).            (* [comment removed for export] *)
        an F_8250c D_8250c.                            (* [comment removed for export] *)
        an F_82510 D_82510.                            (* [comment removed for export] *)
        an F_82514 D_82514.                            (* [comment removed for export] *)
        an F_80710 D_80710.                            (* [comment removed for export] *)
        an F_80714 D_80714.                            (* [comment removed for export] *)
        ab_ft F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
        ab_ft F_8071c D_8071c ltac:(condz).            (* [comment removed for export] *)
        an F_80720 D_80720.                            (* [comment removed for export] *)
        fsw F_80724 D_80724 (at_ sp (-52)).            (* [comment removed for export] *)
        an F_80728 D_80728.                            (* [comment removed for export] *)
        rt F_8072c D_8072c.                            (* [comment removed for export] *)
        ab_tk F_82518 D_82518 ltac:(condz).            (* [comment removed for export] *)
        ab_tk F_82558 D_82558 ltac:(condz).            (* [comment removed for export] *)
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End FAIL.
End MFOPOST.
End FPGen.
End AsAllocM9h.
Require Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM9k.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9m OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Definition mod_ret' (regs r : bvmap 5 word) (sp ra s0v s1v s2v res : word) : Prop :=
  getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
  /\ regs_agree (fun i : reg => In i mod_clob) regs r.

Section MODK.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.

  Theorem mmapordie_katsD :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v size name : word) (PGP CF : Z) (Qok Qf : config -> Prop)
           (GRANT : Model -> word -> Prop) (MOK : Model -> word -> Model),
    let M1 := mod_m1 mem sp ra s0v s1v s2v s3v s4v s5v size name PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := LE4 0xffffffffaaaaaaaa in
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = size -> getr regs 11 = name ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra ->
    (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63) -> U name <> 0 ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok ASEGS mem (at_ sp (-320)) 320 = true ->
    rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn ASEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0] ->
    rdn ASEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    hid_off Hd 0xff250 8 -> hid_off Hd PGP 8 -> hid_off Hd 0xff260 8 -> hid_off Hd (CF + 260) 1 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd (U sp - 320) 320 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (forall mdlm (a : word), same_but_materialized model mdlm -> GRANT mdlm a ->
        AIMGHI <= U a /\ U a + U size < 2 ^ 63 /\ (U a + U size <= U sp - 320 \/ U sp <= U a)) ->
    (* [comment removed for export] *)
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 0 -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 34 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          (forall a : word, GRANT mdlm a ->
              katwD ASEGS (mkCfg (mkst (regupd r1 10 a) (0x80740 : word) (zfill a size M1) rom) (MOK mdlm a)) Qok' Qf') ->
          katD ASEGS (mkCfg (mkst (regupd r1 10 ENOMEMw) (0x80740 : word) M1 rom) mdlm) Qf' ->
          katsD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf') ->
    (* [comment removed for export] *)
    (forall mdlm (a : word), same_but_materialized model mdlm -> MInv A mdlm -> GRANT mdlm a ->
        m_halted (MOK mdlm a) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm a)) A /\ MInv A (MOK mdlm a)) ->
    (* [comment removed for export] *)
    (forall (a : word) (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> GRANT mdlm a -> same_but_materialized (MOK mdlm a) mdl4 -> MInv A mdl4 ->
        mod_ret' regs r' sp ra s0v s1v s2v a ->
        katwD ASEGS (mkCfg (mkst r' ra (wbytes (zfill a size M1) (at_ sp (-40)) SCR) rom) mdl4) Qok Qf) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized mdlm mdl4 -> MInv A mdl4 ->
        mod_ret' regs r' sp ra s0v s1v s2v (Z_to_bv 64 0) ->
        katD ASEGS (mkCfg (mkst r' ra (wbytes (wbytes M1 (at_ sp (-40)) SCR) (at_ sp (-40)) (LE4 12)) rom) mdl4) Qf) ->
    katsD ASEGS (mkCfg (mkst regs (0x82004 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v size name PGP CF Qok Qf GRANT MOK M1 ENOMEMw SCR
           H1 H2 H10 H11 H8 H9 H18 H19 H20 H21 Hsp Hret Hsize Hname HPGP HCF Hstk Rgpg Rpg Rgcf Rdpm Rlim
           HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI SEP NODE CHILD CONTOK CONTKP.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range size) as Hszr.
    destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2].
    assert (Hstk' : store_ok ASEGS (mrestrict Hd mem) (at_ sp (-320)) 320 = true).
    { rewrite store_ok_mrestrict; [exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HDscr]. }
    assert (CELLR : forall (c : Z) (k : nat) v, 0 <= c < 2 ^ 32 -> Z.of_nat k <= 8 -> hid_off Hd c (Z.of_nat k) ->
               rdn ASEGS mem (Z_to_bv 64 c) k = Some v -> rdn ASEGS (mrestrict Hd mem) (Z_to_bv 64 c) k = Some v).
    { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (mod_pre (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v size name PGP CF regs
                H1 H2 H10 H11 H8 H9 H18 H19 H20 H21 Hsp Hsize Hname (conj PG1 PG2) (conj CF1 CF2) Hstk'
                (CELLR 0xff250 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgpg Rgpg) (CELLR PGP 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpg Rpg)
                (CELLR 0xff260 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLR (CF + 260) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDdpm Rdpm))
      as (r1 & RUN1 & B1 & B2 & B8 & B9 & B18 & B10 & B11 & B12 & B13 & B14 & B15 & B17 & AG1).
    assert (EM1 : mod_m1 (mrestrict Hd mem) sp ra s0v s1v s2v s3v s4v s5v size name PGP = mrestrict Hd M1).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1, mod_m1 in G in change_no_check G' end).
      rewrite !wbytes_mrestrict; [reflexivity | | | | | | | | | | | | | | | | | | | | | | | |];
        wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | intros x Hx; apply HDscr; lia]. }
    rewrite EM1 in RUN1.
    assert (M1hid : forall a : word, Hd a = true -> M1 a = mem a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mod_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v size name PGP Hsp).
      destruct (Z_lt_le_dec (U a) (U sp - 320)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katsD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst regs (0x82004 : word) mem rom)
             (mkst r1 (0x8073c : word) (mrestrict Hd M1) rom) model Qok Qf LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN1. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x82004 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M1 M1hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    apply (katsD_ecall ASEGS r1 (0x8073c : word) M1 rom mdlm W_80734 Qok Qf HALTm F_80734 E_80734).
    rewrite B17.
    assert (POSTF : forall MZ : word -> option byte,
               (forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) ->
               store_ok ASEGS (mrestrict Hd MZ) (at_ sp (-40)) 4 = true
               /\ (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v)] ->
                      rdn ASEGS (mrestrict Hd MZ) (at_ sp k) 8 = Some (LE8 v))).
    { intros MZ EZ. split.
      - rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite (store_ok_ext ASEGS 4 M1 MZ); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia].
        eapply store_ok_mono; [apply mod_m1_grows|].
        eapply (store_ok_sub ASEGS mem (at_ sp (-320)) _ 320); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
      - intros k v Hin.
        assert (Hk : -32 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        rewrite rdn_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite <- (mod_m1_slots mem sp ra s0v s1v s2v s3v s4v s5v size name PGP Hsp k v Hin). fold M1.
        apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Q1 : forall v : word, getr (regupd r1 10 v) 1 = Z_to_bv 64 0x8208c) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B1).
    assert (Q2 : forall v : word, getr (regupd r1 10 v) 2 = at_ sp (-48)) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B2).
    assert (Q9 : forall v : word, getr (regupd r1 10 v) 9 = size) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B9).
    assert (Q10 : forall v : word, getr (regupd r1 10 v) 10 = v) by (intros v; rewrite getr_same by (intros E; discriminate E); reflexivity).
    assert (AGC : forall (v : word) (r2 : bvmap 5 word), regs_agree (fun i : reg => In i mod_clob) (regupd r1 10 v) r2 ->
                    regs_agree (fun i : reg => In i mod_clob) regs r2).
    { intros v r2 AG2 x Hx. rewrite (AG2 x Hx).
      assert (NE10 : x <> 10%bv) by (intros ->; apply Hx; (lazymatch goal with |- ?G => let G' := eval unfold mod_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      rewrite getr_other by (intros E; apply NE10; exact E). apply AG1. exact Hx. }
    assert (HIDW : forall (MM : word -> option byte) bs (a : word), Hd a = true -> Z.of_nat (length bs) = 4 -> wbytes MM (at_ sp (-40)) bs a = MM a).
    { intros MM bs a Ha Hl.
      destruct (Z_lt_le_dec (U a) (U sp - 40)) as [C|C]; [apply wbytes_below; rewrite ?Hl, ?at_u by lia; lia|].
      destruct (Z_lt_le_dec (U a) (U sp - 36)) as [C'|C']; [exfalso; rewrite (HDscr a) in Ha by lia; discriminate Ha|].
      apply wbytes_above. rewrite Hl, at_u by lia. lia. }
    assert (L4a : Z.of_nat (length SCR) = 4) by ((lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity).
    assert (L4b : Z.of_nat (length (LE4 12)) = 4) by (rewrite length_N_to_le_bytes; reflexivity).
    apply (NODE mdlm r1 SBMm MIm HALTm B10 B11 B12 B13 B14 B15 Qok Qf).
    - (* [comment removed for export] *)
      intros a GR. destruct (SEP mdlm a SBMm GR) as (SL1 & SL2 & SL3). pose proof (u64_range a) as Har.
      destruct (CHILD mdlm a SBMm MIm GR) as (HOK1 & HOK2 & HOK3).
      set (MZ := zfill a size M1).
      assert (EZ : forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end); apply zfill_out; lia).
      destruct (POSTF MZ EZ) as [SOKZ SLZ].
      assert (CELLZ : forall (c : Z) (k : nat) v, 0 <= c -> c + Z.of_nat k <= AIMGHI -> hid_off Hd c (Z.of_nat k) ->
                 rdn ASEGS mem (Z_to_bv 64 c) k = Some v -> rdn ASEGS (mrestrict Hd MZ) (Z_to_bv 64 c) k = Some v).
      { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [| first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh].
        rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end). rewrite zfill_out by lia. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mod_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v size name PGP Hsp). left. lia. }
      destruct (mod_ok (mrestrict Hd MZ) rom sp ra s0v s1v s2v size CF (regupd r1 10 a)
                  (Q1 a) (Q2 a) (Q9 a) Hsp Hret (conj CF1 CF2) SOKZ
                  (SLZ (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  (SLZ (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  a (Q10 a) ltac:(lia)
                  (CELLZ 0xff260 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLZ (CF + 144) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDlim Rlim))
        as (r2 & RUN2 & C10 & C2 & C1 & C8 & C9 & C18 & AG2).
      rewrite wbytes_mrestrict in RUN2; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                          | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      apply (katwD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst (regupd r1 10 a) (0x80740 : word) MZ rom)
               (mkst r2 ra (mrestrict Hd (wbytes MZ (at_ sp (-40)) SCR)) rom) (MOK mdlm a) Qok Qf HOK2 AWF HOK3 HOK1).
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst (regupd r1 10 a) (0x80740 : word) MZ rom)) with MZ by reflexivity.
      rewrite (mk_munrestrict_same Hd MZ (wbytes MZ (at_ sp (-40)) SCR)).
      2:{ intros x Hx. apply HIDW; [exact Hx | exact L4a]. }
      apply (CONTOK a r2 mdlm mdl4 SBMm MIm GR SBM4 MI4).
      (lazymatch goal with |- ?G => let G' := eval unfold mod_ret' in G in change_no_check G' end). repeat (split; [assumption|]). exact (AGC a r2 AG2).
    - (* [comment removed for export] *)
      set (MZ := M1).
      assert (EZ : forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; reflexivity).
      destruct (POSTF MZ EZ) as [SOKZ SLZ].
      destruct (mod_fail (mrestrict Hd MZ) rom sp ra s0v s1v s2v (regupd r1 10 ENOMEMw)
                  (Q1 ENOMEMw) (Q2 ENOMEMw) Hsp Hret SOKZ
                  (SLZ (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  (SLZ (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  (Q10 ENOMEMw))
        as (r2 & RUN2 & C10 & C2 & C1 & C8 & C9 & C18 & AG2).
      rewrite !wbytes_mrestrict in RUN2; [| wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      apply (katD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst (regupd r1 10 ENOMEMw) (0x80740 : word) MZ rom)
               (mkst r2 ra (mrestrict Hd (wbytes (wbytes MZ (at_ sp (-40)) SCR) (at_ sp (-40)) (LE4 12))) rom) mdlm Qf).
      { destruct FRm as (_ & _ & Hl & _). rewrite Hl. exact LC. }
      { exact AWF. } { exact MIm. } { exact HALTm. }
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst (regupd r1 10 ENOMEMw) (0x80740 : word) MZ rom)) with MZ by reflexivity.
      rewrite (mk_munrestrict_same Hd MZ (wbytes (wbytes MZ (at_ sp (-40)) SCR) (at_ sp (-40)) (LE4 12))).
      2:{ intros x Hx. rewrite (HIDW _ _ x Hx L4b). apply (HIDW _ _ x Hx L4a). }
      apply (CONTKP r2 mdlm mdl4 SBMm MIm SBM4 MI4).
      (lazymatch goal with |- ?G => let G' := eval unfold mod_ret' in G in change_no_check G' end). repeat (split; [assumption|]). exact (AGC ENOMEMw r2 AG2).
  Qed.
End MODK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NODE2.
  Lemma node2_of_mmap_rw :
    forall (r1 : bvmap 5 word) (M1 rom : word -> option byte) (mdlm : Model) (size : word) (Qok' Qf' : config -> Prop),
    m_halted mdlm = None ->
    getr r1 10 = Z_to_bv 64 0 -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 34 ->
    getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
    0 < U size -> U size mod 4096 = 0 ->
    (exists a : word, grant_ok (Z_to_bv 64 0) mdlm a (U size) = true) ->
    (forall a : word, grant_ok (Z_to_bv 64 0) mdlm a (U size) = true ->
        katwD ASEGS (mkCfg (mkst (regupd r1 10 a) (0x80740 : word) (zfill a size M1) rom) (mmap_model a size mdlm)) Qok' Qf') ->
    katD ASEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 (2 ^ 64 - 12))) (0x80740 : word) M1 rom) mdlm) Qf' ->
    katsD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Proof using.
    intros r1 M1 rom mdlm size Qok' Qf' HALT B10 B11 B12 B13 B14 B15 Hsz Hszal EX KOK KKP.
    pose proof (u64_range size) as Hszr.
    set (ms := epend r1 (0x8073c%bv : word) M1 rom (Z_to_bv 64 222)).
    assert (E0 : ms_gpr ms 0 = Z_to_bv 64 0) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend0; exact B10).
    assert (E1 : ms_gpr ms 1 = size) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend1; exact B11).
    assert (PRU : page_round_up_Z (U size) = U size) by (apply page_round_up_Z_aligned; [lia | (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hszal]).
    assert (PRW : page_round_up (ms_gpr ms 1) = size).
    { (lazymatch goal with |- ?G => let G' := eval unfold page_round_up in G in change_no_check G' end). rewrite E1, PRU. apply Z_to_bv_bv_unsigned. }
    assert (ARGS : mmap_args_ok ms).
    { (lazymatch goal with |- ?G => let G' := eval unfold mmap_args_ok in G in change_no_check G' end). rewrite E1. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.ms_gpr_epend2, AsKSys6.MhKSys.ms_gpr_epend3, AsKSys6.MhKSys.ms_gpr_epend4, AsKSys6.MhKSys.ms_gpr_epend5.
      split; [intros X; apply (f_equal bv_unsigned) in X; rewrite u_Z2bv in X by lia; lia|].
      split; [exact B12|]. split; [exact B13|]. split; [rewrite B14; apply bv_eq; reflexivity | exact B15]. }
    apply (katsD_mmap_rw ASEGS ms mdlm (Z_to_bv 64 222) HALT eq_refl ltac:(rewrite u_Z2bv by lia; reflexivity) ARGS Qok' Qf').
    - rewrite E0, E1, PRU. exact EX.
    - intros e He. (lazymatch goal with |- ?G => let G' := eval unfold mmrw_fail, ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_set_epend.
      assert (Ee : e = ENOMEM) by (destruct He as [<-|[]]; reflexivity). subst e.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2 ^ 64 - 12) : word) by (apply bv_eq; vm_compute; reflexivity).
      replace (v_addi (0x8073c%bv : word) 4) with (0x80740%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact KKP.
    - intros a Ha. rewrite E0, E1, PRU in Ha. (lazymatch goal with |- ?G => let G' := eval unfold mmrw_grant in G in change_no_check G' end). rewrite PRW. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_zeros1_epend.
      replace (v_addi (0x8073c%bv : word) 4) with (0x80740%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact (KOK a Ha).
  Qed.
End NODE2.
End FPGen1.
End AsAllocM9k.
Module AsDepotMod.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
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

Definition mo_clob : list reg := [1; 2; 8; 9; 18; 19; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

Definition mo_m1 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v size name raw : word) (PGP : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 s3v))
    (at_ sp (-44)) (LE4 34))
    (at_ sp (-56)) (LE8 (Z_to_bv 64 0x81e7c)))
    (at_ sp (-64)) (LE8 raw))
    (at_ sp (-72)) (LE8 name))
    (at_ sp (-80)) (LE8 size))
    (at_ sp (-88)) (LE8 (Z_to_bv 64 PGP)))
    (at_ sp (-96)) (LE8 s4v))
    (at_ sp (-104)) (LE8 s5v).
#[local] Hint Unfold mo_m1 : asfr.

Section MOPRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v size name raw : word) (PGP CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = size.
  Hypothesis H11 : getr regs 11 = name.
  Hypothesis H12 : getr regs 12 = raw.
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

  #[local] Abbreviation M1 := (mo_m1 mem sp ra s0v s1v s2v s3v s4v s5v size name raw PGP).

  Lemma mo_pre :
    exists r, msteps ASEGS (mkst regs (0x81e08 : word) mem rom) (mkst r (0x8073c : word) M1 rom)
      /\ getr r 1 = Z_to_bv 64 0x81e98 /\ getr r 2 = at_ sp (-48)
      /\ getr r 8 = raw /\ getr r 9 = name /\ getr r 18 = size /\ getr r 19 = Z_to_bv 64 PGP
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = size /\ getr r 12 = Z_to_bv 64 3 /\ getr r 13 = Z_to_bv 64 34
      /\ getr r 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr r 15 = Z_to_bv 64 0 /\ getr r 17 = Z_to_bv 64 222
      /\ regs_agree (fun i : reg => In i mo_clob) regs r.
  Proof using Rdpm Rgcf Rpg Rgpg Hstk HCF HPGP Hname Hsize Hsp H21 H20 H19 H18 H9 H8 H12 H11 H10 H2 H1 CF.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range size) as Hsr. pose proof (u64_range name) as Hnr.
    destruct Hsize as [Hsz1 Hsz2].
    wd_eexists. split.
    - an F_81e00 D_81e00.                              (* [comment removed for export] *)
      fsd F_81e04 D_81e04 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_81e08 D_81e08 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_81e0c D_81e0c (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_81e10 D_81e10 (at_ sp (-32)).              (* [comment removed for export] *)
      fsd F_81e14 D_81e14 (at_ sp (-40)).              (* [comment removed for export] *)
      an F_81e18 D_81e18.                              (* [comment removed for export] *)
      an F_81e1c D_81e1c.                              (* [comment removed for export] *)
      an F_81e20 D_81e20.                              (* [comment removed for export] *)
      cld8 F_81e24 D_81e24 (Z_to_bv 64 PGP) Rgpg.      (* [comment removed for export] *)
      cld8 F_81e28 D_81e28 (Z_to_bv 64 4096) Rpg.      (* [comment removed for export] *)
      an F_81e2c D_81e2c.                              (* [comment removed for export] *)
      ab_tk F_81e30 D_81e30 ltac:(condz).              (* [comment removed for export] *)
      an F_81e40 D_81e40.                              (* [comment removed for export] *)
      an F_81e44 D_81e44.                              (* [comment removed for export] *)
      ab_ft F_81e48 D_81e48 ltac:(condz).              (* [comment removed for export] *)
      av F_81e4c D_81e4c (Z_to_bv 64 (U size + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_81e50 D_81e50 (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_81e54 D_81e54 (Z_to_bv 64 (U size + 4095)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av_and F_81e58 D_81e58 size
        ltac:(rewrite v_and_m4k; unorm; replace (U size + 4095 - (U size + 4095) mod 4096)%Z with (U size) by (Z.div_mod_to_equations; lia); apply Z_to_bv_bv_unsigned).   (* [comment removed for export] *)
      an F_81e5c D_81e5c.                              (* [comment removed for export] *)
      fsw F_81e60 D_81e60 (at_ sp (-44)).              (* [comment removed for export] *)
      an F_81e64 D_81e64.                              (* [comment removed for export] *)
      an F_81e68 D_81e68.                              (* [comment removed for export] *)
      an F_81e6c D_81e6c.                              (* [comment removed for export] *)
      an F_81e70 D_81e70.                              (* [comment removed for export] *)
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
      fld F_82c30 D_82c30 (Z_to_bv 64 0x81e7c).        (* [comment removed for export] *)
      fld F_82c34 D_82c34 raw.                         (* [comment removed for export] *)
      fld F_82c38 D_82c38 name.                        (* [comment removed for export] *)
      fld F_82c3c D_82c3c size.                        (* [comment removed for export] *)
      fld F_82c40 D_82c40 (Z_to_bv 64 PGP).            (* [comment removed for export] *)
      fld F_82c44 D_82c44 s4v.                         (* [comment removed for export] *)
      fld F_82c48 D_82c48 s5v.                         (* [comment removed for export] *)
      an F_82c4c D_82c4c.                              (* [comment removed for export] *)
      rt F_82c50 D_82c50.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 34) (v := Z_to_bv 64 34);
          [exact F_81e74 | reflexivity | exact D_81e74
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold mo_m1 in G in change_no_check G' end);
            repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]);
            apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
          | reflexivity]
        | step_simpl]; rewrite (v_lw_small 34) by lia; vn.   (* [comment removed for export] *)
      an F_81e78 D_81e78.                              (* [comment removed for export] *)
      an F_81e7c D_81e7c.                              (* [comment removed for export] *)
      an F_81e80 D_81e80.                              (* [comment removed for export] *)
      an F_81e84 D_81e84.                              (* [comment removed for export] *)
      an F_81e88 D_81e88.                              (* [comment removed for export] *)
      an F_81e8c D_81e8c.                              (* [comment removed for export] *)
      an F_80730 D_80730.                              (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold mo_clob in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma mo_m1_outside : forall x : word, (U x < U sp - 320 \/ U sp <= U x)%Z -> M1 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mo_m1 in G in change_no_check G' end).
    repeat (rewrite wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma mo_m1_grows : mem_grows mem M1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mo_m1 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma mo_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v)]%Z -> rdn ASEGS M1 (at_ sp k) 8 = Some (LE8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mo_m1 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
End MOPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MOPOST.
  Variables (M2 rom : word -> option byte) (sp ra s0v s1v s2v s3v size : word) (CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x81e98.
  Hypothesis H2 : getr regs 2 = at_ sp (-48).
  Hypothesis H18 : getr regs 18 = size.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hsok : store_ok ASEGS M2 (at_ sp (-48)) 4 = true.
  Hypothesis S_ra : rdn ASEGS M2 (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS M2 (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS M2 (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS M2 (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn ASEGS M2 (at_ sp (-40)) 8 = Some (LE8 s3v).

  Definition mo_ret (r : bvmap 5 word) (res : word) : Prop :=
    getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
    /\ regs_agree (fun i : reg => In i mo_clob) regs r.

  (* [comment removed for export] *)
  Section OK.
    Variable map : word.
    Hypothesis H10 : getr regs 10 = map.
    Hypothesis Hmap : (U map < 2 ^ 63)%Z.
    Hypothesis Rgcf : rdn ASEGS M2 (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)).
    Hypothesis Rlim : rdn ASEGS M2 (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
    Lemma mo_ok :
      exists r, msteps ASEGS (mkst regs (0x80740 : word) M2 rom)
                             (mkst r ra (wbytes M2 (at_ sp (-48)) (LE4 0xffffffffaaaaaaaa)) rom) /\ mo_ret r map.
    Proof using Rlim Rgcf Hmap H10 S_s3 S_s2 S_s1 S_s0 S_ra Hsok HCF Hret Hsp H18 H2 H1 CF size.
      (lazymatch goal with |- ?G => let G' := eval unfold mo_ret in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. pose proof (u64_range map) as Har.
      wd_eexists. split.
      - rt F_80738 D_80738.                            (* [comment removed for export] *)
        an F_81e90 D_81e90.                            (* [comment removed for export] *)
        an F_81e94 D_81e94.                            (* [comment removed for export] *)
        an F_81e98 D_81e98.                            (* [comment removed for export] *)
        an F_80710 D_80710.                            (* [comment removed for export] *)
        an F_80714 D_80714.                            (* [comment removed for export] *)
        ab_tk F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
        an F_80728 D_80728. sltu0.                     (* [comment removed for export] *)
        rt F_8072c D_8072c.                            (* [comment removed for export] *)
        an F_81e9c D_81e9c.                            (* [comment removed for export] *)
        an F_81ea0 D_81ea0.                            (* [comment removed for export] *)
        fsw F_81ea4 D_81ea4 (at_ sp (-48)).            (* [comment removed for export] *)
        an F_81ea8 D_81ea8.                            (* [comment removed for export] *)
        an F_81eac D_81eac.                            (* [comment removed for export] *)
        an F_81eb0 D_81eb0.                            (* [comment removed for export] *)
        an F_80710 D_80710.                            (* [comment removed for export] *)
        an F_80714 D_80714.                            (* [comment removed for export] *)
        ab_tk F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
        an F_80728 D_80728. sltu0.                     (* [comment removed for export] *)
        rt F_8072c D_8072c.                            (* [comment removed for export] *)
        ab_ft F_81eb4 D_81eb4 ltac:(condz).            (* [comment removed for export] *)
        an F_81eb8 D_81eb8.                            (* [comment removed for export] *)
        an F_81ebc D_81ebc.                            (* [comment removed for export] *)
        an F_7c614 D_7c614.                            (* [comment removed for export] *)
        cld8 F_7c618 D_7c618 (Z_to_bv 64 CF) Rgcf.     (* [comment removed for export] *)
        cld8 F_7c61c D_7c61c (Z_to_bv 64 0) Rlim.      (* [comment removed for export] *)
        ab_tk F_7c620 D_7c620 ltac:(condz).            (* [comment removed for export] *)
        rt F_7c63c D_7c63c.                            (* [comment removed for export] *)
        an F_81ec0 D_81ec0.                            (* [comment removed for export] *)
        cld8 F_81ec4 D_81ec4 ra S_ra.                  (* [comment removed for export] *)
        cld8 F_81ec8 D_81ec8 s0v S_s0.                 (* [comment removed for export] *)
        cld8 F_81ecc D_81ecc s1v S_s1.                 (* [comment removed for export] *)
        cld8 F_81ed0 D_81ed0 s2v S_s2.                 (* [comment removed for export] *)
        cld8 F_81ed4 D_81ed4 s3v S_s3.                 (* [comment removed for export] *)
        an F_81ed8 D_81ed8.                            (* [comment removed for export] *)
        aret F_81edc D_81edc ra.                       (* [comment removed for export] *)
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mo_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End OK.

  (* [comment removed for export] *)
  Section DIE.
    Hypothesis H10 : getr regs 10 = Z_to_bv 64 (2 ^ 64 - 12).
    Hypothesis Hstk2 : store_ok ASEGS M2 (at_ sp (-96)) 48 = true.
    Hypothesis Rdie1 : rdn ASEGS M2 (Z_to_bv 64 0xff2b0) 8 = Some (LE8 (Z_to_bv 64 1)).
    Hypothesis Rdie2 : rdn ASEGS M2 (Z_to_bv 64 0x19909c) 4 = Some (LE4 0).
    Lemma mo_die :
      exists r M', msteps ASEGS (mkst regs (0x80740 : word) M2 rom) (mkst r (0x7bfb4 : word) M' rom).
    Proof using Rdie2 Rdie1 Hstk2 H10 Hsok Hsp H18 H2 H1 size sp.
      pose proof (u64_range sp) as Hspr.
      wd_eexists. wd_eexists.
      rt F_80738 D_80738.                            (* [comment removed for export] *)
      an F_81e90 D_81e90.                            (* [comment removed for export] *)
      an F_81e94 D_81e94.                            (* [comment removed for export] *)
      an F_81e98 D_81e98.                            (* [comment removed for export] *)
      an F_80710 D_80710.                            (* [comment removed for export] *)
      an F_80714 D_80714.                            (* [comment removed for export] *)
      ab_ft F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
      ab_tk F_8071c D_8071c ltac:(condz).            (* [comment removed for export] *)
      an F_80728 D_80728.                            (* [comment removed for export] *)
      rt F_8072c D_8072c.                            (* [comment removed for export] *)
      an F_81e9c D_81e9c.                            (* [comment removed for export] *)
      an F_81ea0 D_81ea0.                            (* [comment removed for export] *)
      fsw F_81ea4 D_81ea4 (at_ sp (-48)).            (* [comment removed for export] *)
      an F_81ea8 D_81ea8.                            (* [comment removed for export] *)
      an F_81eac D_81eac.                            (* [comment removed for export] *)
      an F_81eb0 D_81eb0.                            (* [comment removed for export] *)
      an F_80710 D_80710.                            (* [comment removed for export] *)
      an F_80714 D_80714.                            (* [comment removed for export] *)
      ab_ft F_80718 D_80718 ltac:(condz).            (* [comment removed for export] *)
      ab_ft F_8071c D_8071c ltac:(condz).            (* [comment removed for export] *)
      an F_80720 D_80720.                            (* [comment removed for export] *)
      fsw F_80724 D_80724 (at_ sp (-48)).            (* [comment removed for export] *)
      an F_80728 D_80728.                            (* [comment removed for export] *)
      rt F_8072c D_8072c.                            (* [comment removed for export] *)
      ab_tk F_81eb4 D_81eb4 ltac:(condz).            (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 12) (v := Z_to_bv 64 12);
          [exact F_81ef0 | reflexivity | exact D_81ef0
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
            apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
          | reflexivity]
        | step_simpl]; rewrite (v_lw_small 12) by lia; vn.   (* [comment removed for export] *)
      an F_81ef4 D_81ef4.                            (* [comment removed for export] *)
      an F_81ef8 D_81ef8.                            (* [comment removed for export] *)
      an F_81efc D_81efc.                            (* [comment removed for export] *)
      an F_81f00 D_81f00.                            (* [comment removed for export] *)
      an F_81f04 D_81f04.                            (* [comment removed for export] *)
      an F_81f08 D_81f08.                            (* [comment removed for export] *)
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
End MOPOST.
End FPGen.
End AsDepotMod.
Module AsDepotModK.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9m AsAllocM9k OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 AsDepotMod.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Definition mo_ret' (regs r : bvmap 5 word) (sp ra s0v s1v s2v s3v res : word) : Prop :=
  getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
  /\ regs_agree (fun i : reg => In i mo_clob) regs r.

(* [comment removed for export] *)
Lemma mo_spin : forall (r : bvmap 5 word) (M rom : word -> option byte) (model : Model),
  to_spin ASEGS (mkst r (0x7bfb4%bv : word) M rom) model.
Proof using.
  intros r M rom model.
  apply (ts_spin_of_step_j ASEGS (mkst r (0x7bfb4%bv : word) M rom) model W_7bfac 0 0 4%Z);
    [reflexivity | exact F_7bfac | reflexivity | exact D_7bfac | reflexivity | reflexivity].
Qed.

Section MOK.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.

  Theorem mo_katD :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v size name raw : word) (PGP CF : Z) (Q : config -> Prop)
           (GRANT : Model -> word -> Prop) (MOK : Model -> word -> Model),
    let M1 := mo_m1 mem sp ra s0v s1v s2v s3v s4v s5v size name raw PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := LE4 0xffffffffaaaaaaaa in
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = size -> getr regs 11 = name -> getr regs 12 = raw ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra ->
    (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63) -> U name <> 0 ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok ASEGS mem (at_ sp (-320)) 320 = true ->
    rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn ASEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0] ->
    rdn ASEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    rdn ASEGS mem (Z_to_bv 64 0xff2b0) 8 = Some (LE8 (Z_to_bv 64 1)) ->
    rdn ASEGS mem (Z_to_bv 64 0x19909c) 4 = Some (LE4 0) ->
    hid_off Hd 0xff250 8 -> hid_off Hd PGP 8 -> hid_off Hd 0xff260 8 -> hid_off Hd (CF + 260) 1 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd 0xff2b0 8 -> hid_off Hd 0x19909c 4 ->
    hid_off Hd (U sp - 320) 320 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (forall mdlm (a : word), same_but_materialized model mdlm -> GRANT mdlm a ->
        AIMGHI <= U a /\ U a + U size < 2 ^ 63 /\ (U a + U size <= U sp - 320 \/ U sp <= U a)) ->
    (* [comment removed for export] *)
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 0 -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 34 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Q' : config -> Prop,
          (forall a : word, GRANT mdlm a ->
              katD ASEGS (mkCfg (mkst (regupd r1 10 a) (0x80740 : word) (zfill a size M1) rom) (MOK mdlm a)) Q') ->
          doomed ASEGS (mkCfg (mkst (regupd r1 10 ENOMEMw) (0x80740 : word) M1 rom) mdlm) ->
          katD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Q') ->
    (* [comment removed for export] *)
    (forall mdlm (a : word), same_but_materialized model mdlm -> MInv A mdlm -> GRANT mdlm a ->
        m_halted (MOK mdlm a) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm a)) A /\ MInv A (MOK mdlm a)) ->
    (* [comment removed for export] *)
    (forall (a : word) (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> GRANT mdlm a -> same_but_materialized (MOK mdlm a) mdl4 -> MInv A mdl4 ->
        mo_ret' regs r' sp ra s0v s1v s2v s3v a ->
        katD ASEGS (mkCfg (mkst r' ra (wbytes (zfill a size M1) (at_ sp (-48)) SCR) rom) mdl4) Q) ->
    katD ASEGS (mkCfg (mkst regs (0x81e08 : word) mem rom) model) Q.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v size name raw PGP CF Q GRANT MOK M1 ENOMEMw SCR
           H1 H2 H10 H11 H12 H8 H9 H18 H19 H20 H21 Hsp Hret Hsize Hname HPGP HCF Hstk Rgpg Rpg Rgcf Rdpm Rlim Rd1 Rd2
           HDgpg HDpg HDgcf HDdpm HDlim HDd1 HDd2 HDscr HALT LC AWF MI SEP NODE CHILD CONTOK.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range size) as Hszr.
    destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2].
    assert (Hstk' : store_ok ASEGS (mrestrict Hd mem) (at_ sp (-320)) 320 = true).
    { rewrite store_ok_mrestrict; [exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HDscr]. }
    assert (CELLR : forall (c : Z) (k : nat) v, 0 <= c < 2 ^ 32 -> Z.of_nat k <= 8 -> hid_off Hd c (Z.of_nat k) ->
               rdn ASEGS mem (Z_to_bv 64 c) k = Some v -> rdn ASEGS (mrestrict Hd mem) (Z_to_bv 64 c) k = Some v).
    { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (mo_pre (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v size name raw PGP CF regs
                H1 H2 H10 H11 H12 H8 H9 H18 H19 H20 H21 Hsp Hsize Hname (conj PG1 PG2) (conj CF1 CF2) Hstk'
                (CELLR 0xff250 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgpg Rgpg) (CELLR PGP 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpg Rpg)
                (CELLR 0xff260 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLR (CF + 260) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDdpm Rdpm))
      as (r1 & RUN1 & B1 & B2 & B8 & B9 & B18 & B19 & B10 & B11 & B12 & B13 & B14 & B15 & B17 & AG1).
    assert (EM1 : mo_m1 (mrestrict Hd mem) sp ra s0v s1v s2v s3v s4v s5v size name raw PGP = mrestrict Hd M1).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1, mo_m1 in G in change_no_check G' end).
      rewrite !wbytes_mrestrict; [reflexivity | | | | | | | | | | | | | | | | | | | | | | | | | |];
        wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | intros x Hx; apply HDscr; lia]. }
    rewrite EM1 in RUN1.
    assert (M1hid : forall a : word, Hd a = true -> M1 a = mem a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mo_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v size name raw PGP Hsp).
      destruct (Z_lt_le_dec (U a) (U sp - 320)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst regs (0x81e08 : word) mem rom)
             (mkst r1 (0x8073c : word) (mrestrict Hd M1) rom) model Q LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN1. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x81e08 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M1 M1hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    apply (katD_ecall ASEGS r1 (0x8073c : word) M1 rom mdlm W_80734 Q HALTm F_80734 E_80734).
    rewrite B17.
    assert (POSTF : forall MZ : word -> option byte,
               (forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) ->
               store_ok ASEGS (mrestrict Hd MZ) (at_ sp (-48)) 4 = true
               /\ store_ok ASEGS (mrestrict Hd MZ) (at_ sp (-96)) 48 = true
               /\ (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v)] ->
                      rdn ASEGS (mrestrict Hd MZ) (at_ sp k) 8 = Some (LE8 v))).
    { intros MZ EZ.
      assert (SOKZ : forall (o : Z) (n : nat), -320 <= o -> o + Z.of_nat n <= 0 -> store_ok ASEGS (mrestrict Hd MZ) (at_ sp o) n = true).
      { intros o n Ho1 Ho2.
        rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u by lia; intros x Hx; apply HDscr; lia].
        rewrite (store_ok_ext ASEGS n M1 MZ); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; lia].
        eapply store_ok_mono; [apply mo_m1_grows|].
        eapply (store_ok_sub ASEGS mem (at_ sp (-320)) _ 320); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
      split; [apply SOKZ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. split; [apply SOKZ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
      intros k v Hin.
      assert (Hk : -40 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite rdn_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      rewrite <- (mo_m1_slots mem sp ra s0v s1v s2v s3v s4v s5v size name raw PGP Hsp k v Hin). fold M1.
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Q1 : forall v : word, getr (regupd r1 10 v) 1 = Z_to_bv 64 0x81e98) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B1).
    assert (Q2 : forall v : word, getr (regupd r1 10 v) 2 = at_ sp (-48)) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B2).
    assert (Q18 : forall v : word, getr (regupd r1 10 v) 18 = size) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B18).
    assert (Q10 : forall v : word, getr (regupd r1 10 v) 10 = v) by (intros v; rewrite getr_same by (intros E; discriminate E); reflexivity).
    assert (AGC : forall (v : word) (r2 : bvmap 5 word), regs_agree (fun i : reg => In i mo_clob) (regupd r1 10 v) r2 ->
                    regs_agree (fun i : reg => In i mo_clob) regs r2).
    { intros v r2 AG2 x Hx. rewrite (AG2 x Hx).
      assert (NE10 : x <> 10%bv) by (intros ->; apply Hx; (lazymatch goal with |- ?G => let G' := eval unfold mo_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      rewrite getr_other by (intros E; apply NE10; exact E). apply AG1. exact Hx. }
    assert (L4a : Z.of_nat (length SCR) = 4) by ((lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity).
    assert (HIDW : forall (MM : word -> option byte) bs (a : word), Hd a = true -> Z.of_nat (length bs) = 4 -> wbytes MM (at_ sp (-48)) bs a = MM a).
    { intros MM bs a Ha Hl.
      destruct (Z_lt_le_dec (U a) (U sp - 48)) as [C|C]; [apply wbytes_below; rewrite ?Hl, ?at_u by lia; lia|].
      destruct (Z_lt_le_dec (U a) (U sp - 44)) as [C'|C']; [exfalso; rewrite (HDscr a) in Ha by lia; discriminate Ha|].
      apply wbytes_above. rewrite Hl, at_u by lia. lia. }
    apply (NODE mdlm r1 SBMm MIm HALTm B10 B11 B12 B13 B14 B15 Q).
    - (* [comment removed for export] *)
      intros a GR. destruct (SEP mdlm a SBMm GR) as (SL1 & SL2 & SL3). pose proof (u64_range a) as Har.
      destruct (CHILD mdlm a SBMm MIm GR) as (HOK1 & HOK2 & HOK3).
      set (MZ := zfill a size M1).
      assert (EZ : forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end); apply zfill_out; lia).
      destruct (POSTF MZ EZ) as (SOKZ & _ & SLZ).
      assert (CELLZ : forall (c : Z) (k : nat) v, 0 <= c -> c + Z.of_nat k <= AIMGHI -> hid_off Hd c (Z.of_nat k) ->
                 rdn ASEGS mem (Z_to_bv 64 c) k = Some v -> rdn ASEGS (mrestrict Hd MZ) (Z_to_bv 64 c) k = Some v).
      { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [| first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh].
        rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end). rewrite zfill_out by lia. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mo_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v size name raw PGP Hsp). left. lia. }
      destruct (mo_ok (mrestrict Hd MZ) rom sp ra s0v s1v s2v s3v size CF (regupd r1 10 a)
                  (Q1 a) (Q2 a) (Q18 a) Hsp Hret (conj CF1 CF2) SOKZ
                  (SLZ (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  (SLZ (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-40) s3v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  a (Q10 a) ltac:(lia)
                  (CELLZ 0xff260 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLZ (CF + 144) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDlim Rlim))
        as (r2 & RUN2 & C10 & C2 & C1 & C8 & C9 & C18 & C19 & AG2).
      rewrite wbytes_mrestrict in RUN2; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                          | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      apply (katD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst (regupd r1 10 a) (0x80740 : word) MZ rom)
               (mkst r2 ra (mrestrict Hd (wbytes MZ (at_ sp (-48)) SCR)) rom) (MOK mdlm a) Q HOK2 AWF HOK3 HOK1).
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst (regupd r1 10 a) (0x80740 : word) MZ rom)) with MZ by reflexivity.
      rewrite (mk_munrestrict_same Hd MZ (wbytes MZ (at_ sp (-48)) SCR)).
      2:{ intros x Hx. apply HIDW; [exact Hx | exact L4a]. }
      apply (CONTOK a r2 mdlm mdl4 SBMm MIm GR SBM4 MI4).
      (lazymatch goal with |- ?G => let G' := eval unfold mo_ret' in G in change_no_check G' end). repeat (split; [assumption|]). exact (AGC a r2 AG2).
    - (* [comment removed for export] *)
      set (MZ := M1).
      assert (EZ : forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; reflexivity).
      destruct (POSTF MZ EZ) as (SOKZ & SOKZ2 & _).
      assert (CELLM : forall (c : Z) (k : nat) v, 0 <= c -> c + Z.of_nat k <= AIMGHI -> hid_off Hd c (Z.of_nat k) ->
                 rdn ASEGS mem (Z_to_bv 64 c) k = Some v -> rdn ASEGS (mrestrict Hd MZ) (Z_to_bv 64 c) k = Some v).
      { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [| first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh].
        rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        (lazymatch goal with |- ?G => let G' := eval unfold MZ, M1 in G in change_no_check G' end). apply (mo_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v size name raw PGP Hsp). left. lia. }
      destruct (mo_die (mrestrict Hd MZ) rom sp size (regupd r1 10 ENOMEMw) (Q1 ENOMEMw) (Q2 ENOMEMw) (Q18 ENOMEMw) Hsp SOKZ (Q10 ENOMEMw) SOKZ2
                  (CELLM 0xff2b0 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDd1 Rd1) (CELLM 0x19909c 4%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDd2 Rd2))
        as (r2 & M'2 & RUN2).
      apply (doomed_msteps_acct ASEGS Hd HOFFSEG WX A (mkst (regupd r1 10 ENOMEMw) (0x80740 : word) MZ rom) (mkst r2 (0x7bfb4 : word) M'2 rom) mdlm).
      { destruct FRm as (_ & _ & Hl & _). rewrite Hl. exact LC. }
      { exact AWF. } { exact MIm. } { exact HALTm. }
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      apply doomed_to_spin; [apply mo_spin|].
      pose proof (same_but_materialized_frame mdlm mdl4 SBM4) as (_&_&_&_&_&_&_&_&_&_&_&_&Hh4&_). rewrite Hh4. exact HALTm.
  Qed.
End MOK.

(* [comment removed for export] *)
Section NODEDM.
  Lemma node_dm_of_mmap_rw :
    forall (r1 : bvmap 5 word) (M1 rom : word -> option byte) (mdlm : Model) (size : word) (Q' : config -> Prop),
    m_halted mdlm = None ->
    getr r1 10 = Z_to_bv 64 0 -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 34 ->
    getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
    0 < U size -> U size mod 4096 = 0 ->
    (exists a : word, grant_ok (Z_to_bv 64 0) mdlm a (U size) = true) ->
    (forall a : word, grant_ok (Z_to_bv 64 0) mdlm a (U size) = true ->
        katD ASEGS (mkCfg (mkst (regupd r1 10 a) (0x80740 : word) (zfill a size M1) rom) (mmap_model a size mdlm)) Q') ->
    doomed ASEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 (2 ^ 64 - 12))) (0x80740 : word) M1 rom) mdlm) ->
    katD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Q'.
  Proof using.
    intros r1 M1 rom mdlm size Q' HALT B10 B11 B12 B13 B14 B15 Hsz Hszal EX KOK KKP.
    pose proof (u64_range size) as Hszr.
    set (ms := epend r1 (0x8073c%bv : word) M1 rom (Z_to_bv 64 222)).
    assert (E0 : ms_gpr ms 0 = Z_to_bv 64 0) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend0; exact B10).
    assert (E1 : ms_gpr ms 1 = size) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend1; exact B11).
    assert (PRU : page_round_up_Z (U size) = U size) by (apply page_round_up_Z_aligned; [lia | (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hszal]).
    assert (PRW : page_round_up (ms_gpr ms 1) = size).
    { (lazymatch goal with |- ?G => let G' := eval unfold page_round_up in G in change_no_check G' end). rewrite E1, PRU. apply Z_to_bv_bv_unsigned. }
    assert (ARGS : mmap_args_ok ms).
    { (lazymatch goal with |- ?G => let G' := eval unfold mmap_args_ok in G in change_no_check G' end). rewrite E1. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.ms_gpr_epend2, AsKSys6.MhKSys.ms_gpr_epend3, AsKSys6.MhKSys.ms_gpr_epend4, AsKSys6.MhKSys.ms_gpr_epend5.
      split; [intros X; apply (f_equal bv_unsigned) in X; rewrite u_Z2bv in X by lia; lia|].
      split; [exact B12|]. split; [exact B13|]. split; [rewrite B14; apply bv_eq; reflexivity | exact B15]. }
    apply (katD_mmap_rw_dm ASEGS ms mdlm (Z_to_bv 64 222) Q' HALT eq_refl ltac:(rewrite u_Z2bv by lia; reflexivity) ARGS).
    - rewrite E0, E1, PRU. exact EX.
    - intros e He. (lazymatch goal with |- ?G => let G' := eval unfold mmrw_fail, ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_set_epend.
      assert (Ee : e = ENOMEM) by (destruct He as [<-|[]]; reflexivity). subst e.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2 ^ 64 - 12) : word) by (apply bv_eq; vm_compute; reflexivity).
      replace (v_addi (0x8073c%bv : word) 4) with (0x80740%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact KKP.
    - intros a Ha. rewrite E0, E1, PRU in Ha. (lazymatch goal with |- ?G => let G' := eval unfold mmrw_grant in G in change_no_check G' end). rewrite PRW. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_zeros1_epend.
      replace (v_addi (0x8073c%bv : word) 4) with (0x80740%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact (KOK a Ha).
  Qed.
End NODEDM.
End FPGen1.
End AsDepotModK.
Module AsAllocM9i.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9m AsAllocM9k AsAllocM9h OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 AsDepotMod AsDepotModK.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section MAPOK.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.

  (* [comment removed for export] *)
  Theorem rarmapo_katD :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v addr size name : word) (PGP CF : Z) (Q : config -> Prop)
           (MOK MKP MDS : Model -> Model),
    let M1 := mfo_m1 mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := LE4 0xffffffffaaaaaaaa in
    (* [comment removed for export] *)
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 11 = addr -> getr regs 12 = size -> getr regs 13 = name ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra ->
    U addr mod 4096 = 0 -> (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63) -> U name = 0 ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok ASEGS mem (at_ sp (-368)) 368 = true ->
    rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn ASEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    (* [comment removed for export] *)
    (AIMGHI <= U addr /\ U addr + U size < 2 ^ 63 /\ (U addr + U size <= U sp - 368 \/ U sp <= U addr)) ->
    (* [comment removed for export] *)
    hid_off Hd 0xff250 8 -> hid_off Hd PGP 8 -> hid_off Hd 0xff260 8 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd (U sp - 368) 368 ->
    (* [comment removed for export] *)
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = addr -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Q' : config -> Prop,
          katD ASEGS (mkCfg (mkst (regupd r1 10 addr) (0x80740 : word) (zfill addr size M1) rom) (MOK mdlm)) Q' ->
          doomed ASEGS (mkCfg (mkst (regupd r1 10 ENOMEMw) (0x80740 : word) M1 rom) (MKP mdlm)) ->
          doomed ASEGS (mkCfg (mkst (regupd r1 10 ENOMEMw) (0x80740 : word) (unfill addr size M1) rom) (MDS mdlm)) ->
          katD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Q') ->
    (* [comment removed for export] *)
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))
        /\ (m_halted (MDS mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MDS mdlm)) A /\ MInv A (MDS mdlm))) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        mfi_ret regs r' sp ra s0v s1v s2v s3v s4v addr ->
        katD ASEGS (mkCfg (mkst r' ra (wbytes (zfill addr size M1) (at_ sp (-52)) SCR) rom) mdl4) Q) ->
    (* [comment removed for export] *)
    (forall (MZ : word -> option byte) (r2 : bvmap 5 word), (MZ = M1 \/ MZ = unfill addr size M1) ->
        getr r2 2 = at_ sp (-96) -> getr r2 8 = size -> getr r2 9 = Z_to_bv 64 0 -> getr r2 18 = addr -> getr r2 19 = ENOMEMw ->
        exists fx' (r3 : bvmap 5 word) (M3 : word -> option byte),
          msteps ASEGS (@mkst fx r2 (0x82578 : word) (mrestrict Hd (wbytes (wbytes MZ (at_ sp (-52)) SCR) (at_ sp (-52)) (LE4 12))) rom)
                       (@mkst fx' r3 (0x7bfb4 : word) M3 rom)) ->
    katD ASEGS (mkCfg (mkst regs (0x8a7d4 : word) mem rom) model) Q.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v addr size name PGP CF Q MOK MKP MDS M1 ENOMEMw SCR
           H1 H2 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Haddr Hsize Hname HPGP HCF Hstk Rgpg Rpg Rgcf Rlim
           Hslot HDgpg HDpg HDgcf HDlim HDscr HALT LC AWF MI NODE CHILD CONTOK DIE.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range addr) as Har. pose proof (u64_range size) as Hszr.
    destruct Hslot as (SL1 & SL2 & SL3). destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2].
    (* [comment removed for export] *)
    assert (Hstk' : store_ok ASEGS (mrestrict Hd mem) (at_ sp (-368)) 368 = true).
    { rewrite store_ok_mrestrict; [exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HDscr]. }
    assert (CELLR : forall (c : Z) (k : nat) v, 0 <= c < 2 ^ 32 -> Z.of_nat k <= 8 -> hid_off Hd c (Z.of_nat k) ->
               rdn ASEGS mem (Z_to_bv 64 c) k = Some v -> rdn ASEGS (mrestrict Hd mem) (Z_to_bv 64 c) k = Some v).
    { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (mfo_pre (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v addr size name PGP regs
                H1 H2 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Haddr Hsize Hname (conj PG1 PG2) Hstk'
                (CELLR 0xff250 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgpg Rgpg) (CELLR PGP 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpg Rpg))
      as (r1 & RUN1 & B1 & B2 & B8 & B9 & B18 & B19 & B20 & B10 & B11 & B12 & B13 & B14 & B15 & B17 & AG1).
    assert (EM1 : mfo_m1 (mrestrict Hd mem) sp ra s0v s1v s2v s3v s4v s5v addr size name PGP = mrestrict Hd M1).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1, mfo_m1, mfo_m0 in G in change_no_check G' end).
      rewrite !wbytes_mrestrict; [reflexivity | | | | | | | | | | | | | | | | | | | | | | | | | | | |];
        wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | intros x Hx; apply HDscr; lia]. }
    rewrite EM1 in RUN1.
    assert (M1hid : forall a : word, Hd a = true -> M1 a = mem a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mfo_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp).
      destruct (Z_lt_le_dec (U a) (U sp - 368)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst regs (0x8a7d4 : word) mem rom)
             (mkst r1 (0x8073c : word) (mrestrict Hd M1) rom) model Q LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN1. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x8a7d4 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M1 M1hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    (* [comment removed for export] *)
    apply (katD_ecall ASEGS r1 (0x8073c : word) M1 rom mdlm W_80734 Q HALTm F_80734 E_80734).
    rewrite B17.
    destruct (CHILD mdlm SBMm MIm) as ((HOK1 & HOK2 & HOK3) & (HKP1 & HKP2 & HKP3) & (HDS1 & HDS2 & HDS3)).
    (* [comment removed for export] *)
    assert (POSTF : forall MZ : word -> option byte,
               (forall x : word, U sp - 368 <= U x < U sp -> MZ x = M1 x) ->
               store_ok ASEGS (mrestrict Hd MZ) (at_ sp (-52)) 4 = true
               /\ (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v)] ->
                      rdn ASEGS (mrestrict Hd MZ) (at_ sp k) 8 = Some (LE8 v))).
    { intros MZ EZ. split.
      - rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite (store_ok_ext ASEGS 4 M1 MZ); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia].
        eapply store_ok_mono; [apply mfo_m1_grows|].
        eapply (store_ok_sub ASEGS mem (at_ sp (-368)) _ 368); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
      - intros k v Hin.
        assert (Hk : -48 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        rewrite rdn_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite <- (mfo_m1_slots mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp k v Hin). fold M1.
        apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Q1 : forall v : word, getr (regupd r1 10 v) 1 = Z_to_bv 64 0x824fc) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B1).
    assert (Q2 : forall v : word, getr (regupd r1 10 v) 2 = at_ sp (-96)) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B2).
    assert (Q8 : forall v : word, getr (regupd r1 10 v) 8 = size) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B8).
    assert (Q9 : forall v : word, getr (regupd r1 10 v) 9 = Z_to_bv 64 0) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B9).
    assert (Q10 : forall v : word, getr (regupd r1 10 v) 10 = v) by (intros v; rewrite getr_same by (intros E; discriminate E); reflexivity).
    assert (AGC : forall (v : word) (r2 : bvmap 5 word), regs_agree (fun i : reg => In i mfi_clob2) (regupd r1 10 v) r2 ->
                    regs_agree (fun i : reg => In i mfi_clob2) regs r2).
    { intros v r2 AG2 x Hx. rewrite (AG2 x Hx).
      assert (NE10 : x <> 10%bv) by (intros ->; apply Hx; (lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      rewrite getr_other by (intros E; apply NE10; exact E). apply AG1. exact Hx. }
    assert (HIDW : forall (MM : word -> option byte) bs (a : word), Hd a = true -> Z.of_nat (length bs) = 4 -> wbytes MM (at_ sp (-52)) bs a = MM a).
    { intros MM bs a Ha Hl.
      destruct (Z_lt_le_dec (U a) (U sp - 52)) as [C|C]; [apply wbytes_below; rewrite ?Hl, ?at_u by lia; lia|].
      destruct (Z_lt_le_dec (U a) (U sp - 48)) as [C'|C']; [exfalso; rewrite (HDscr a) in Ha by lia; discriminate Ha|].
      apply wbytes_above. rewrite Hl, at_u by lia. lia. }
    apply (NODE mdlm r1 SBMm MIm HALTm B10 B11 B12 B13 B14 B15 Q).
    - (* [comment removed for export] *)
      set (MZ := zfill addr size M1).
      assert (EZ : forall x : word, U sp - 368 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end); apply zfill_out; lia).
      destruct (POSTF MZ EZ) as [SOKZ SLZ].
      assert (CELLZ : forall (c : Z) (k : nat) v, 0 <= c -> c + Z.of_nat k <= AIMGHI -> hid_off Hd c (Z.of_nat k) ->
                 rdn ASEGS mem (Z_to_bv 64 c) k = Some v -> rdn ASEGS (mrestrict Hd MZ) (Z_to_bv 64 c) k = Some v).
      { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [| first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh].
        rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end). rewrite zfill_out by lia. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mfo_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp). left. lia. }
      destruct (mfo_ok (mrestrict Hd MZ) rom sp ra s0v s1v s2v s3v s4v addr size CF (regupd r1 10 addr)
                  (Q1 addr) (Q2 addr) (Q8 addr) Hsp Hret (conj CF1 CF2) SOKZ
                  (SLZ (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  (SLZ (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-40) s3v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-48) s4v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  (Q10 addr) ltac:(lia)
                  (CELLZ 0xff260 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLZ (CF + 144) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDlim Rlim))
        as (r2 & RUN2 & C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & AG2).
      rewrite wbytes_mrestrict in RUN2; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                          | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      apply (katD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst (regupd r1 10 addr) (0x80740 : word) MZ rom)
               (mkst r2 ra (mrestrict Hd (wbytes MZ (at_ sp (-52)) SCR)) rom) (MOK mdlm) Q HOK2 AWF HOK3 HOK1).
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst (regupd r1 10 addr) (0x80740 : word) MZ rom)) with MZ by reflexivity.
      rewrite (mk_munrestrict_same Hd MZ (wbytes MZ (at_ sp (-52)) SCR)).
      2:{ intros a Ha. apply HIDW; [exact Ha | (lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity]. }
      apply (CONTOK r2 mdlm mdl4 SBMm MIm SBM4 MI4).
      (lazymatch goal with |- ?G => let G' := eval unfold mfi_ret in G in change_no_check G' end). repeat (split; [assumption|]). exact (AGC addr r2 AG2).
    - (* [comment removed for export] *)
      set (MZ := M1).
      assert (EZ : forall x : word, U sp - 368 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; reflexivity).
      destruct (POSTF MZ EZ) as [SOKZ SLZ].
      destruct (mfo_fail (mrestrict Hd MZ) rom sp size (regupd r1 10 ENOMEMw) (Q1 ENOMEMw) (Q2 ENOMEMw) (Q8 ENOMEMw) (Q9 ENOMEMw) Hsp SOKZ (Q10 ENOMEMw))
        as (r2 & RUN2 & C2 & C8 & C9 & C19 & C18 & C20 & AG2).
      assert (L4a : Z.of_nat (length SCR) = 4) by ((lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity).
      assert (L4b : Z.of_nat (length (LE4 12)) = 4) by (rewrite length_N_to_le_bytes; reflexivity).
      rewrite !wbytes_mrestrict in RUN2; [| rewrite ?L4a, ?L4b, ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia
                                           | rewrite ?L4a, ?L4b, ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      assert (C18' : getr r2 18 = addr) by (rewrite C18; rewrite getr_other by (intros E; discriminate E); exact B18).
      destruct (DIE MZ r2 ltac:(left; reflexivity) C2 C8 C9 C18' C19) as (fx' & r3 & M3 & RUN3).
      apply (doomed_msteps_acct ASEGS Hd HOFFSEG WX A (mkst (regupd r1 10 ENOMEMw) (0x80740 : word) MZ rom)
               (@mkst fx' r3 (0x7bfb4 : word) M3 rom) (MKP mdlm) HKP2 AWF HKP3 HKP1).
      { rewrite mk_restrict_mkst. eapply msteps_trans; [exact RUN2 | exact RUN3]. }
      intros mdl4 MI4 SBM4 HC4.
      apply doomed_to_spin; [apply mo_spin|].
      pose proof (same_but_materialized_frame (MKP mdlm) mdl4 SBM4) as (_&_&_&_&_&_&_&_&_&_&_&_&Hh4&_). rewrite Hh4. exact HKP1.
    - (* [comment removed for export] *)
      set (MZ := unfill addr size M1).
      assert (EZ : forall x : word, U sp - 368 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end); apply unfill_out; lia).
      destruct (POSTF MZ EZ) as [SOKZ SLZ].
      destruct (mfo_fail (mrestrict Hd MZ) rom sp size (regupd r1 10 ENOMEMw) (Q1 ENOMEMw) (Q2 ENOMEMw) (Q8 ENOMEMw) (Q9 ENOMEMw) Hsp SOKZ (Q10 ENOMEMw))
        as (r2 & RUN2 & C2 & C8 & C9 & C19 & C18 & C20 & AG2).
      assert (L4a : Z.of_nat (length SCR) = 4) by ((lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity).
      assert (L4b : Z.of_nat (length (LE4 12)) = 4) by (rewrite length_N_to_le_bytes; reflexivity).
      rewrite !wbytes_mrestrict in RUN2; [| rewrite ?L4a, ?L4b, ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia
                                           | rewrite ?L4a, ?L4b, ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      assert (C18' : getr r2 18 = addr) by (rewrite C18; rewrite getr_other by (intros E; discriminate E); exact B18).
      destruct (DIE MZ r2 ltac:(right; reflexivity) C2 C8 C9 C18' C19) as (fx' & r3 & M3 & RUN3).
      apply (doomed_msteps_acct ASEGS Hd HOFFSEG WX A (mkst (regupd r1 10 ENOMEMw) (0x80740 : word) MZ rom)
               (@mkst fx' r3 (0x7bfb4 : word) M3 rom) (MDS mdlm) HDS2 AWF HDS3 HDS1).
      { rewrite mk_restrict_mkst. eapply msteps_trans; [exact RUN2 | exact RUN3]. }
      intros mdl4 MI4 SBM4 HC4.
      apply doomed_to_spin; [apply mo_spin|].
      pose proof (same_but_materialized_frame (MDS mdlm) mdl4 SBM4) as (_&_&_&_&_&_&_&_&_&_&_&_&Hh4&_). rewrite Hh4. exact HDS1.
  Qed.

End MAPOK.
End FPGen1.
End AsAllocM9i.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMRunSf.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Section RUNSF.
  Variables (mem MP : word -> option byte) (S : word) (n : Z) (x18 x19 x22 x23 x24 x25 x26 x27 : word).
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis Pfoot : forall x : word, MP x <> mem x -> (U S - 2272 <= U x < U S)%Z.
  Hypothesis Pgrows : mem_grows mem MP.
  #[local] Abbreviation MA := (ma_A MP S n x18 x19 x22 x23 x24 x25 x26 x27).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation spL := (at_ S (-2320)).
  #[local] Abbreviation MF := (ms_pre_mem S n MA).

  Lemma msf_MA : forall x : word, (U x < U S - 2416 \/ U S - 2272 <= U x)%Z -> MF x = MA x.
  Proof using GS.
    intros x Hx. pose proof (u64_range S) as HSr. destruct GS as [G1 G2]. (lazymatch goal with |- ?G => let G' := eval unfold ms_pre_mem, la_m0, cbs_m0 in G in change_no_check G' end).
    repeat (rewrite wbytes_outside; [ | rewrite length_N_to_le_bytes, ?at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, ?at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma msf_outside : forall x : word, (U x < U S - 2416 \/ U S <= U x)%Z -> MF x = mem x.
  Proof using Pfoot GS.
    intros x Hx. rewrite msf_MA by lia. rewrite (ma_A_outside MP S n x18 x19 x22 x23 x24 x25 x26 x27 GS) by lia.
    destruct (decide (MP x = mem x)) as [E | NE]; [exact E|]. pose proof (Pfoot x NE). lia.
  Qed.
  Lemma msf_above : forall x : word, (U S - 2128 <= U x)%Z -> MF x = MP x.
  Proof using GS. intros x Hx. rewrite msf_MA by lia. apply (ma_A_outside MP S n x18 x19 x22 x23 x24 x25 x26 x27 GS). lia. Qed.
  Lemma msf_grows : mem_grows mem MF.
  Proof using Pgrows.
    eapply mem_grows_trans; [exact Pgrows|]. apply (mem_grows_trans _ MA); [exact (ma_A_grows MP S n x18 x19 x22 x23 x24 x25 x26 x27)|].
    (lazymatch goal with |- ?G => let G' := eval unfold ms_pre_mem, la_m0, cbs_m0 in G in change_no_check G' end). do 18 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
  Qed.
  Lemma msf_rd_above : forall (k : Z) (w : nat) (bs : list byte), (-2128 <= k)%Z -> (k + Z.of_nat w <= 0)%Z ->
    rdn ASEGS MP (at_ S k) w = Some bs -> rdn ASEGS MF (at_ S k) w = Some bs.
  Proof using GS.
    intros k w bs K1 K2 Hr. pose proof (u64_range S). destruct GS as [G1 G2]. rewrite <- Hr.
    apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply msf_above. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma msf_slotsA : forall (k : Z) (v : word), In (k, v) (ma_slotsA S n x18 x19 x22 x23 x24 x25 x26 x27) ->
    rdn ASEGS MF (at_ S k) 8 = Some (LE8 v).
  Proof using GS.
    intros k v Hin. pose proof (u64_range S) as HSr. pose proof GS as [G1 G2].
    pose proof (ma_slotsA_range S n x18 x19 x22 x23 x24 x25 x26 x27 k v Hin) as [Hk1 Hk2].
    assert (OUT : rdn ASEGS MF (at_ S k) 8 = rdn ASEGS MA (at_ S k) 8).
    { apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply msf_MA. lia. }
    rewrite OUT. unfold ma_slotsA in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval unfold ma_A in G in change_no_check G' end); rewrite ?at_at; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); rd8_chain |]).
    destruct Hin.
  Qed.
  (* [comment removed for export] *)
  Lemma msf_cb_slots : forall (o : Z) (v : word),
    In (o, v) [(-8, Z_to_bv 64 0x4bdc4); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048)]%Z ->
    rdn ASEGS MF (at_ sp2 o) 8 = Some (LE8 v).
  Proof using GS.
    intros o v Hin. pose proof (u64_range S) as HSr. destruct GS as [G1 G2]. (lazymatch goal with |- ?G => let G' := eval unfold ms_pre_mem, la_m0, cbs_m0 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rewrite ?at_at; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); rd8_chain |]). destruct Hin.
  Qed.
  Lemma msf_la_slots : forall (o : Z) (v : word),
    In (o, v) [(-8, Z_to_bv 64 0x50324); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048);
               (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x103f18); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)]%Z ->
    rdn ASEGS MF (at_ spL o) 8 = Some (LE8 v).
  Proof using GS.
    intros o v Hin. pose proof (u64_range S) as HSr. destruct GS as [G1 G2]. (lazymatch goal with |- ?G => let G' := eval unfold ms_pre_mem, la_m0, cbs_m0 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rewrite ?at_at; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); rd8_chain |]). destruct Hin.
  Qed.
End RUNSF.
End FPGen.
End AsAllocMRunSf.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMSecDefs.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9a.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Definition sec_hx (mp n a : Z) : Prop :=
  let p := mp + sec_user_off n in
  a = p - 16
  \/ (mp + PG <= a < mp + PG + 16)
  \/ (SB + (mp + PG) / 8 <= a < SB + p / 8)
  \/ (SB + (p + n + 7) / 8 <= a < SB + (mp + sec_map_size n) / 8).

Lemma mmap_except_vm : forall a n m, same_except_vm m (mmap_model a n m).
Proof. intros a n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Section WithCeil.
Context {RC : run_ceil}.

Section SECDEFS.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  #[local] Abbreviation T := (bt_thread bt).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition runS_st (st : ast) (mp n : Z) (grow : bool) (d' : depot) (naa' : list (Z * Z)) : ast :=
    depot_st (op_sec_alloc (op_meter st EVT [] 0) mp n grow) d' naa'.

  (* [comment removed for export] *)
  Definition runS_post (st : ast) (Lc FF : list (Z * Z)) (R : bvmap 5 word) (M : mem) (mdl : Model) (n : Z) (c' : config) : Prop :=
    exists fx' (R' : bvmap 5 word) (M' M0 : mem) (mdl' : Model) (mp : Z) (grow : bool) (d' : depot) (naa' : list (Z * Z))
           (id : Z) (x18 x19 : word),
      let S := getr R 2 in
      let p := mp + sec_user_off n in
      let st' := runS_st st mp n grow d' naa' in
      c' = mkCfg (@mkst fx' R' (Z_to_bv 64 0x4bed0) M' (seg_rom ASEGS)) mdl'
      /\ FXOK fx' /\ m_halted mdl' = None /\ BackingAlgebra.model_ivs_wf mdl'
      /\ WF bt st' ((p, n) :: Lc) FF /\ Rep bt st' ((p, n) :: Lc) FF M0 mdl'
      (* [comment removed for export] *)
      /\ mp mod PG = 0 /\ dyn_ok (bt_ia bt) mp (mp + sec_map_size n)
      /\ (forall lo hi, In (lo, hi) (all_ranges bt st) -> mp + sec_map_size n <= lo \/ hi <= mp)
      /\ range_allowed (a_aa st') (sh_lo mp) (sh_hi mp (sec_map_size n))
      (* [comment removed for export] *)
      /\ (forall a : word, M' a <> M0 a -> sec_hx mp n (U a) /\ M' a <> None)
      (* [comment removed for export] *)
      /\ (forall a : word, M' a <> M a ->
            ((U S - 3584 <= U a < U S) \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a)) /\ M' a <> None)
      (* [comment removed for export] *)
      /\ (forall (k0 : Z) (v : word),
             In (k0, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
             rdn ASEGS M' (at_ S k0) 8 = Some (LE8 v))
      /\ (forall (k0 : Z) (v : word),
             In (k0, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
             rdn ASEGS M' (at_ S k0) 8 = Some (LE8 v))
      /\ (forall a : word, U S - MSTK_A <= U a < U S -> M' a <> None /\ store_ok ASEGS M' a 1%nat = true)
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      /\ getr R' 2 = at_ S (-2272) /\ getr R' 4 = getr R 4 /\ getr R' 3 = getr R 3
      /\ getr R' 8 = Z_to_bv 64 0 /\ getr R' 9 = Z_to_bv 64 n /\ getr R' 10 = Z_to_bv 64 id /\ getr R' 18 = Z_to_bv 64 (mp + PG)
      /\ getr R' 19 = Z_to_bv 64 (sec_needed n) /\ getr R' 20 = Z_to_bv 64 p /\ getr R' 21 = Z_to_bv 64 (p - 16)
      /\ getr R' 22 = Z_to_bv 64 0x103f18 /\ getr R' 23 = at_ S (-2128) /\ getr R' 24 = Z_to_bv 64 0
      /\ getr R' 25 = Z_to_bv 64 (p + n) /\ getr R' 26 = Z_to_bv 64 T /\ getr R' 27 = Z_to_bv 64 1
      /\ 0 <= id < 2 ^ 32
      /\ same_except_vm mdl mdl'
      /\ lazy_kept (bt_ia bt) Lc FF mdl mdl'.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition sec_frames (fx : FPState) (R : bvmap 5 word) (n : Z) (rq : bvmap 5 word) (Mq : mem) : Prop :=
    exists (x18 x19 : word) (sz : Z) (bsz : list byte),
      let S := getr R 2 in
      la_regs (at_ S (-2320)) (Z_to_bv 64 0x1041c8) (sec_needed n) rq /\ getr rq 21 = Z_to_bv 64 8
      /\ getr rq 4 = getr R 4 /\ getr rq 3 = getr R 3 /\ getr rq 26 = Z_to_bv 64 T /\ getr rq 27 = Z_to_bv 64 1
      /\ (forall (k0 : Z) (v : word), In (k0, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
             rdn ASEGS Mq (at_ S k0) 8 = Some (LE8 v))
      /\ (forall (k0 : Z) (v : word),
             In (k0, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
             rdn ASEGS Mq (at_ S k0) 8 = Some (LE8 v))
      /\ rdn ASEGS Mq (at_ S (-2120)) 4 = Some (LE4 sz) /\ rdn ASEGS Mq (at_ S (-2120)) 8 = Some bsz /\ length bsz = 8%nat /\ (1 <= sz <= 8 /\ bytes_le_to_Z bsz = sz)
      /\ rdn ASEGS Mq (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))
      /\ (forall (o : Z) (v : word),
             In (o, v) [(-8, Z_to_bv 64 0x4bdc4); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048)]%Z ->
             rdn ASEGS Mq (at_ (at_ S (-2272)) o) 8 = Some (LE8 v))
      /\ (forall (o : Z) (v : word),
             In (o, v) [(-8, Z_to_bv 64 0x50324); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048);
                        (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x103f18); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)]%Z ->
             rdn ASEGS Mq (at_ (at_ S (-2320)) o) 8 = Some (LE8 v))
      /\ (forall a : word, U S - MSTK_A <= U a < U S -> Mq a <> None /\ store_ok ASEGS Mq a 1%nat = true).

  (* [comment removed for export] *)
  Definition at_sec_null (fx : FPState) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (n : Z) (st : ast) (c' : config) : Prop :=
    exists (rq : bvmap 5 word) (Mq : mem) (mdlq : Model),
      let S := getr R 2 in
      c' = mkCfg (@mkst fx rq (Z_to_bv 64 0x50610) Mq (seg_rom ASEGS)) mdlq
      /\ m_halted mdlq = None /\ BackingAlgebra.model_ivs_wf mdlq
      /\ Rep bt st Lc FF Mq mdlq
      /\ getr rq 10 = Z_to_bv 64 0 /\ sec_frames fx R n rq Mq
      /\ (forall a : word, Mq a <> M a -> U S - 2736 <= U a < U S)
      /\ same_except_vm mdl mdlq /\ lazy_kept (bt_ia bt) Lc FF mdl mdlq.

  (* [comment removed for export] *)
  Definition at_sec_grant (fx : FPState) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (n : Z) (st : ast) (c' : config) : Prop :=
    exists (rq : bvmap 5 word) (Mq : mem) (mdlq : Model) (a : word),
      let S := getr R 2 in
      let msz := sec_map_size n in
      c' = mkCfg (@mkst fx rq (Z_to_bv 64 0x50610) Mq (seg_rom ASEGS)) mdlq
      /\ AsKSys10.chunk_child mdl mdlq a (Z_to_bv 64 msz) /\ MInv (a_aa st) mdlq
      /\ dyn_ok (bt_ia bt) (U a) (U a + msz) /\ U a mod PG = 0
      /\ (forall lo hi, In (lo, hi) (all_ranges bt st) -> U a + msz <= lo \/ hi <= U a)
      /\ (forall b0 n0, In (b0, n0) (bt_maps0 bt) -> U a + msz <= U b0 \/ U b0 + U n0 <= U a)
      /\ getr rq 10 = a /\ sec_frames fx R n rq Mq
      /\ (forall x : word, Mq x <> M x -> (U S - 2736 <= U x < U S) \/ (U a <= U x < U a + msz))
      /\ (forall x : word, U a <= U x < U a + msz -> Mq x = Some (Z_to_bv 8 0))
      /\ mem_grows M Mq
      /\ same_except_vm mdl mdlq.

  (* [comment removed for export] *)
  Definition partBs_stmt (HPf : option Z -> ast -> Prop) : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st : ast) (c' : config),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> bounds st Lc B C K -> HPf h st -> hole_ok h n ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 64512 < n <= NMAX -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      (forall st', (forall c, a_reg st' c = a_reg st c /\ a_cache st' c = a_cache st c) -> a_kact st' = a_kact st + kcost_malloc n -> HPf None st') ->
      runS_post st Lc FF R M mdl n c' ->
      katD ASEGS c' (malloc_ok ASEGS FXOK asan_addrs (fun h0 => AAINVP (HPf h0) bt) MSTK_A R M mdl Lc FF B C K ret n sp).
End SECDEFS.
End WithCeil.
End AsAllocMSecDefs.
Require Stdlib.NArith.NArith OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotBud2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMSecK.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvLedger OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4.AsAllocM4s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotBud2.

Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Lemma la_msz_sec : forall n, la_msz (sec_needed n) = sec_map_size n.
Proof. intros n. (lazymatch goal with |- ?G => let G' := eval unfold la_msz, sec_map_size, RoundUp, PG in G in change_no_check G' end). f_equal. f_equal. f_equal. lia. Qed.

Lemma sec_msz_bnd : forall n, 64512 < n -> sec_map_size n mod 4096 = 0 /\ n + 8192 <= sec_map_size n <= n + 12294.
Proof.
  intros n Hn. pose proof (sec_needed_bnd n Hn) as B. rewrite <- la_msz_sec. (lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end).
  pose proof (Z.div_mod (sec_needed n + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sec_needed n + 4095) 4096 ltac:(lia)).
  split; [rewrite Z.add_comm, Z.mul_comm; rewrite <- (Z.mul_1_r 4096) at 1; rewrite <- Z.mul_add_distr_l, Z.mul_comm; apply Z_mod_mult | lia].
Qed.


(* [comment removed for export] *)
Lemma zfill_in_s : forall (a n : word) m (x : word),
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> zfill a n m x = Some (Z_to_bv 8 0).
Proof.
  intros a n m x Hx. (lazymatch goal with |- ?G => let G' := eval unfold zfill, AllocSim.zmem in G in change_no_check G' end).
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.
Lemma zfill_grows_s : forall (a n : word) (Mb : word -> option byte), mem_grows Mb (zfill a n Mb).
Proof. intros a n Mb x Hx. (lazymatch goal with |- ?G => let G' := eval unfold zfill, AllocSim.zmem in G in change_no_check G' end). destruct (_ && _)%bool; [discriminate | exact Hx]. Qed.

(* [comment removed for export] *)
Abbreviation sec_shs := sec_hull.

Lemma sec_naa_bytes : forall mp n, A_bytes (sec_naa mp n) = sec_hull mp n.
Proof. intros mp n. (lazymatch goal with |- ?G => let G' := eval unfold sec_naa, sec_hull in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [A_bytes fst snd] in G in change_no_check G' end). lia. Qed.

Lemma sec_shs_bnd : forall mp n, 0 <= mp -> 64512 < n -> 0 <= sec_hull mp n <= n / 8 + 9730.
Proof.
  intros mp n Hmp Hn. destruct (sec_msz_bnd n Hn) as [M1 M2]. (lazymatch goal with |- ?G => let G' := eval unfold sec_hull, sec_hull_lo, sec_hull_hi, pgup, pgdn, PG, sh_hi, sh_lo, SB in G in change_no_check G' end).
  replace (4096 - 1) with 4095 by reflexivity.
  pose proof (Z.div_mod (0x7fff8000 + mp / 8) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + mp / 8) 4096 ltac:(lia)).
  pose proof (Z.div_mod (0x7fff8000 + (mp + sec_map_size n + 7) / 8 + 4095) 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (0x7fff8000 + (mp + sec_map_size n + 7) / 8 + 4095) 4096 ltac:(lia)).
  pose proof (Z.div_mod mp 8 ltac:(lia)). pose proof (Z.mod_pos_bound mp 8 ltac:(lia)).
  pose proof (Z.div_mod (mp + sec_map_size n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (mp + sec_map_size n + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
  lia.
Qed.
Lemma sec_naa_wf : forall A mp n, A_wf A -> 0 <= mp -> 64512 < n -> A_wf (A ++ sec_naa mp n).
Proof.
  intros A mp n AW Hmp Hn. (lazymatch goal with |- ?G => let G' := eval unfold sec_naa, sec_hull_lo, sec_hull_hi, pgup, pgdn in G in change_no_check G' end). apply A_wf_snoc; [exact AW | | apply Z_mod_mult | apply Z_mod_mult].
  pose proof (sec_shs_bnd mp n Hmp Hn) as B. unfold sec_hull, sec_hull_lo, sec_hull_hi, pgup, pgdn in B. lia.
Qed.
Lemma sec_naa_allowed : forall A mp n, 0 <= mp -> mp + sec_map_size n <= 2 ^ 47 -> 64512 < n ->
  range_allowed (A ++ sec_naa mp n) (sh_lo mp) (sh_hi mp (sec_map_size n)).
Proof.
  intros A mp n Hmp Hhi Hn a Ha. destruct (sec_msz_bnd n Hn) as [M1 M2].
  assert (Ra : 0 <= a < 2 ^ 64).
  { unfold sh_lo, sh_hi, SB in Ha. pose proof (Z.div_mod mp 8 ltac:(lia)). pose proof (Z.mod_pos_bound mp 8 ltac:(lia)).
    pose proof (Z.div_mod (mp + sec_map_size n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (mp + sec_map_size n + 7) 8 ltac:(lia)). lia. }
  (lazymatch goal with |- ?G => let G' := eval unfold page_allowedb in G in change_no_check G' end). apply existsb_exists. exists (sh_lo mp / 4096 * 4096, (sh_hi mp (sec_map_size n) + 4095) / 4096 * 4096).
  split; [apply in_app_iff; right; left; (lazymatch goal with |- ?G => let G' := eval unfold sec_hull_lo, sec_hull_hi, pgup, pgdn, PG in G in change_no_check G' end); replace (4096 - 1) with 4095 by reflexivity; reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
  pose proof (page_base_le3 (Z_to_bv 64 a)) as (P1 & P2 & P3). rewrite u_Z2bv in P1, P2 by lia. unfold page_size in *.
  pose proof (Z.div_mod (sh_lo mp) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sh_lo mp) 4096 ltac:(lia)).
  pose proof (Z.div_mod (sh_hi mp (sec_map_size n) + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sh_hi mp (sec_map_size n) + 4095) 4096 ltac:(lia)).
  pose proof (Z.div_mod (U (page_base (Z_to_bv 64 a))) 4096 ltac:(lia)).
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.leb_le].
  - (* [comment removed for export] *)
    assert (Q : sh_lo mp / 4096 <= U (page_base (Z_to_bv 64 a)) / 4096).
    { apply Z.div_le_lower_bound; [lia|]. rewrite P3 in *. lia. }
    rewrite P3 in *. lia.
  - assert (Q : U (page_base (Z_to_bv 64 a)) / 4096 + 1 <= (sh_hi mp (sec_map_size n) + 4095) / 4096).
    { apply Z.div_le_lower_bound; [lia|]. rewrite P3 in *. lia. }
    rewrite P3 in *. lia.
Qed.


(* [comment removed for export] *)
Lemma sec_flags_clear : forall h n st, holes_le h st -> hole_ok h n -> 64512 < n ->
  forall c, r_uhole (a_reg st c) = false /\ r_fhole (a_reg st c) = false.
Proof.
  intros h n st HL HO Hn c.
  assert (NF : ~ (r_uhole (a_reg st c) = true \/ r_fhole (a_reg st c) = true)).
  { intros F. destruct (HL c F) as (n' & E & Hn' & _). destruct HO as [HO | HO]; rewrite HO in E; [discriminate E | injection E as <-; lia]. }
  split; [destruct (r_uhole (a_reg st c)); [exfalso; apply NF; left; reflexivity | reflexivity]
         | destruct (r_fhole (a_reg st c)); [exfalso; apply NF; right; reflexivity | reflexivity]].
Qed.
Lemma sec_holes_none : forall h n st st', holes_le h st -> hole_ok h n -> 64512 < n -> (forall c, a_reg st' c = a_reg st c) -> holes_le None st'.
Proof.
  intros h n st st' HL HO Hn ER c F. exfalso. rewrite ER in F. destruct (sec_flags_clear h n st HL HO Hn c) as [F1 F2].
  destruct F as [F | F]; [rewrite F1 in F | rewrite F2 in F]; discriminate F.
Qed.
Lemma sec_no_holes : forall {RC : run_ceil} bt h n st, holes_le h st -> hole_ok h n -> 64512 < n -> forall z, ~ holes bt st z.
Proof.
  intros RC bt h n st HL HO Hn z (c & _ & [[F _] | [F _]]); destruct (sec_flags_clear h n st HL HO Hn c) as [F1 F2];
    [rewrite F1 in F | rewrite F2 in F]; discriminate F.
Qed.

Section SecK.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.

  (* [comment removed for export] *)
  Theorem sec_pre_budget : forall st Lc FF M0 mdl (B C K n mp : Z),
    Rep bt st Lc FF M0 mdl -> WF bt st Lc FF -> bounds st Lc B C K ->
    64512 < n -> B + (n + MBLK) <= GBUDGET -> K + kcost_malloc n <= KCAP -> 0 <= mp ->
    eager_used mdl + sec_map_size n + 2 ^ 17 + A_bytes (a_aa st) + sec_hull mp n <= vm_limit (m_vmmaps mdl).
  Proof using.
    intros st Lc FF M0 mdl B C K n mp R W (BP & _ & BK) Hn HB HK Hmp.
    destruct (sec_msz_bnd n Hn) as [M1 M2]. pose proof (sec_hull_le mp n Hmp ltac:(lia)) as HL.
    pose proof (budget_core bt st Lc FF (2 ^ 20) (2 ^ 28) W (n + MBLK) 1 ltac:((lazymatch goal with |- ?G => let G' := eval unfold MBLK in G in change_no_check G' end); lia) ltac:(lia)
                  ltac:((lazymatch goal with |- ?G => let G' := eval unfold QCAP in G in change_no_check G' end); lia) ltac:(unfold kcost_malloc in HK; lia)) as BR.
    destruct (ledger_R bt st Lc FF M0 mdl R) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LIM & _).
    destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & BUD & _) & _).
    assert (X8 : sec_map_size n / 8 <= (n + MBLK) / 8) by (apply Z.div_le_mono; (lazymatch goal with |- ?G => let G' := eval unfold MBLK in G in change_no_check G' end); lia).
    unfold ROOMSLACK, MBLK, PG in *. lia.   (* [comment removed for export] *)
  Qed.

  Hypothesis BOK : boot_ok bt.
  Hypothesis BTOT : boot_totals bt.

  (* [comment removed for export] *)
  Theorem sec_grant_ex : forall st Lc FF M0 mdl mdlm n, WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
    a_kact st <= KCAP -> 64513 <= n <= GBUDGET -> eager_used mdl + sec_map_size n + A_bytes (a_aa st) <= vm_limit (m_vmmaps mdl) ->
    exists a : word, grant_ok (Z_to_bv 64 0) mdlm a (sec_map_size n) = true.
  Proof using BTOT BOK.
    intros st Lc FF M0 mdl mdlm n W RP SBM MI KC HN BUD.
    destruct (sbm_vmmaps _ _ SBM) as [EV EL].
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (AW & _) & _).
    pose proof (AsKSys6.AsanNodesMmLib.mat_pages_le_A_bytes (a_aa st) mdlm MI AW) as MP.
    pose proof (eager_used_ext mdlm mdl EV EL) as EE.
    apply (grant_exists bt st Lc FF (2 ^ 20) (2 ^ 28) M0 mdl W ltac:(lia) (qroom_WF bt st Lc FF W) RP KC BOK BTOT (Z_to_bv 64 0) mdlm (sec_map_size n) EV).
    - exact (sec_map_size_NZEX n HN).
    - rewrite vm_backing_used_split, EE, EV. lia.
  Qed.
End SecK.

(* [comment removed for export] *)
Lemma HID_off_segments_l : forall {RC : run_ceil} bt st st' mdl mdl', bt_ia bt = asan_addrs -> rep_ledger bt st mdl -> m_vm_lazy mdl' = m_vm_lazy mdl ->
  H_off_segments ASEGS (HID st' mdl').
Proof.
  intros RC bt st st' mdl mdl' BI RL EL a Ha.
  apply HID_lazy in Ha. pose proof (u64_range a) as Hr.
  assert (L : lzb mdl (U a) = true) by (unfold lzb in Ha |- *; rewrite EL in Ha; exact Ha).
  destruct (lazy_zone bt st mdl (U a) RL ltac:(lia) L) as [Z1 Z2].
  rewrite BI in Z2. cbn [ia_img_lo ia_img_hi asan_addrs] in Z2.
  destruct (find_segment ASEGS (U a) 1) eqn:E; [|reflexivity]. exfalso. apply Z2. apply asanF_segs_hull. rewrite E. discriminate.
Qed.
End AsAllocMSecK.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsAllocMTopA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9m AsAllocM9k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocM2s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1 AsAllocMRunSf AsAllocMSecK AsAllocMSecDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotBud.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac ha_prev := first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

From Stdlib Require Import FunctionalExtensionality.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod4096_mod8s : forall t, t mod 4096 = 0 -> t mod 8 = 0.
Proof. intros t Ht. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma restrict_mkst_s : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

Section WithCeil.
Context {RC : run_ceil}.

(* [comment removed for export] *)
Definition sec_cells (bt : as_boot) : Prop :=
  In (0x103f58, 8%nat, 0x1000) (bt_consts bt)                  (* [comment removed for export] *)
  /\ In (0xff258, 8%nat, 0x1011e8) (bt_consts bt)               (* [comment removed for export] *)
  /\ In (0x1011e8, 8%nat, 0x1a2c0) (bt_consts bt)               (* [comment removed for export] *)
  /\ In (0x103f60, 8%nat, bt_ptrarr bt) (bt_consts bt)          (* [comment removed for export] *)
  /\ In (0x103f68, 8%nat, bt_ptrarr bt) (bt_consts bt)          (* [comment removed for export] *)
  /\ In (0xff2b0, 8%nat, 1) (bt_consts bt) /\ In (0x19909c, 4%nat, 0) (bt_consts bt)
  /\ In (0x1e23c, 8%nat, 0x612079726f6d656d) (bt_consts bt) /\ In (0x1e244, 8%nat, 0x7365726464612074) (bt_consts bt)
  /\ In (0x1e24c, 4%nat, 0x70252073) (bt_consts bt) /\ In (0x1e250, 1%nat, 0) (bt_consts bt)
  /\ In (0x22760, 4%nat, 0x60940) (bt_consts bt) /\ In (0x104b0, 8%nat, 0xaaaaaaaaaaaaaaaa) (bt_consts bt).

Section TOPSA.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis SCELLS : sec_cells bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis BOK : boot_ok bt.
  Hypothesis BTOT : boot_totals bt.
  Hypothesis HTP : TP = ia_tp asan_addrs.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Theorem malloc_sec_to_mmap :
    forall fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp n : Z) (st : ast) (h : option Z) (Qok Qf : config -> Prop),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> holes_le h st -> hole_ok h n ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A -> U (getr R 10) = n -> 64512 < n <= NMAX -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      (forall c', at_sec_grant bt fx R M mdl Lc FF n st c' -> katwD ASEGS c' Qok Qf) ->
      (forall c', at_sec_null bt fx R M mdl Lc FF n st c' -> katD ASEGS c' Qf) ->
      katsD ASEGS (cfg ASEGS fx R (ia_malloc asan_addrs) M mdl) Qok Qf.
  Proof using HTP BTOT BOK BOOTG GEOM SCELLS PCELLS CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros fx R M mdl Lc FF B C K ret sp n st h Qok Qf HFX HH MW W RP BD HPH HO CP HR10 Hn FPC HB HC HK CONT1 CONT0.
    assert (KC : a_kact st <= KCAP) by (destruct BD as (_ & _ & BK); unfold kcost_malloc, EVT in HK; lia).
    assert (Hn34 : 64513 <= n <= 2 ^ 34) by (destruct BD as ((BP & BP2) & _); unfold GBUDGET, MBLK in HB; lia).
    pose proof ceil_rng as CR. pose proof ceil_pg as CPG.
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4. pose proof CP4 as CP4'. rewrite <- HTP in CP4.
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx
                      & CELL_rss & CELL_lmag & CELL_tbl2 & CELL_t16 & CELL_t2048 & CELL_minrz & CELL_maxrz & CELL_maxsz & CELL_sbeg
                      & CELL_cpm & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he & CELL_gfl & CELL_pp & CELL_mfs & CELL_fill
                      & CELL_grm & CELL_rm & CELL_glsn & CELL_lsn & CELL_magic & CELL_hook & CELL_thr64 & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9).
    pose proof GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _ & OBL_rt_private & _).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_rt_private_stmt in OBL_rt_private.
    hidehyp GCT.
    (* [comment removed for export] *)
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & _ & SB1). hidehyp GCB.
    hidehyp GTB.
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi asan_addrs] in GTI, GCI.
    pose proof (u64_range S) as HSr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, KSPACE, NMAX in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st Lc FF M mdl z W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). tauto. }
    destruct R14 as (Bw1 & Bw2 & Bw3 & Bw4 & Bw5).
    set (Mr := mrestrict Hd M).
    Ltac hoff NH := apply hid_off_of; intros z Hz; unfold T_UNW, T_QC, T_PC, PC_SZ in *; split; [lia | apply NH; lia].
    Ltac konst Hd M R1 NHs C := apply (cellZ_restrict Hd M _ _ _ (const_cell bt M _ _ _ R1 C)); [lia | lia | hoff NHs].
    (* [comment removed for export] *)
    assert (K_mcs : rdn ASEGS Mr (Z_to_bv 64 0x10827c) 4 = Some (LE4 30)) by konst Hd M R1 NHs CELL_mcs.
    assert (K_gcf : rdn ASEGS Mr (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8))) by konst Hd M R1 NHs CELL_gcf.
    assert (K_fum : rdn ASEGS Mr (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_fum.
    assert (K_inited : rdn ASEGS Mr (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_inited.
    assert (K_pg : rdn ASEGS Mr (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP))) by konst Hd M R1 NHs CELL_pg.
    assert (K_P : rdn ASEGS Mr (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096))) by konst Hd M R1 NHs CELL_P.
    assert (K_kif : rdn ASEGS Mr (Z_to_bv 64 0x106de0) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_kif.
    assert (K_key : rdn ASEGS Mr (at_ (Z_to_bv 64 0x106de0) 4) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 0x106de0) 4) with (Z_to_bv 64 0x106de4 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_key. }
    assert (K_tsdp : rdn ASEGS Mr (at_ tp (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by (apply bv_eq; rewrite at_u by (rewrite CP4; wd_ulia_c); rewrite CP4; wd_ulia_c). konst Hd M R1 NHs CELL_tsdp. }
    assert (K_tctx : rdn ASEGS Mr (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))) by konst Hd M R1 NHs CELL_tctx.
    assert (K_rss : rdn ASEGS Mr (Z_to_bv 64 0x1897e2) 1 = Some [Z_to_bv 8 0]) by konst Hd M R1 NHs CELL_rss.
    assert (K_lmag : rdn ASEGS Mr (Z_to_bv 64 0x10490) 8 = Some (LE8 MAGICw)).
    { (lazymatch goal with |- ?G => let G' := eval unfold MAGICw in G in change_no_check G' end). konst Hd M R1 NHs CELL_lmag. }
    assert (K_tbl2 : rdn ASEGS Mr (at_ (Z_to_bv 64 0x10500) 4) 1 = Some [Z_to_bv 8 3]).
    { replace (at_ (Z_to_bv 64 0x10500) 4) with (Z_to_bv 64 0x10504 : word) by (apply bv_eq; reflexivity). rewrite <- w2b1 by lia. konst Hd M R1 NHs CELL_tbl2. }
    assert (K_t16 : rdn ASEGS Mr (at_ (Z_to_bv 64 0x10600) 8) 1 = Some [Z_to_bv 8 4]).
    { replace (at_ (Z_to_bv 64 0x10600) 8) with (Z_to_bv 64 0x10608 : word) by (apply bv_eq; reflexivity). rewrite <- w2b1 by lia. konst Hd M R1 NHs CELL_t16. }
    assert (K_t2048 : rdn ASEGS Mr (at_ (Z_to_bv 64 0x10600) 49) 1 = Some [Z_to_bv 8 11]).
    { replace (at_ (Z_to_bv 64 0x10600) 49) with (Z_to_bv 64 0x10631 : word) by (apply bv_eq; reflexivity). rewrite <- w2b1 by lia. konst Hd M R1 NHs CELL_t2048. }
    assert (K_minrz : rdn ASEGS Mr (at_ (Z_to_bv 64 0x103f18) 3624) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 16))).
    { replace (at_ (Z_to_bv 64 0x103f18) 3624) with (Z_to_bv 64 0x104d40 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_minrz. }
    assert (K_maxrz : rdn ASEGS Mr (at_ (Z_to_bv 64 0x103f18) 3626) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 2048))).
    { replace (at_ (Z_to_bv 64 0x103f18) 3626) with (Z_to_bv 64 0x104d42 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_maxrz. }
    assert (K_maxsz : rdn ASEGS Mr (at_ (Z_to_bv 64 0x103f18) 3616) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 40)))).
    { replace (at_ (Z_to_bv 64 0x103f18) 3616) with (Z_to_bv 64 0x104d38 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_maxsz. }
    assert (K_sbeg : rdn ASEGS Mr (at_ (Z_to_bv 64 0x103f18) 32) 8 = Some (LE8 (Z_to_bv 64 SBEG))).
    { replace (at_ (Z_to_bv 64 0x103f18) 32) with (Z_to_bv 64 0x103f38 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_sbeg. }
    (* [comment removed for export] *)
    Ltac thr_cell Hd M NHrt C := apply (cellZ_restrict Hd M _ _ _ C); [(lazymatch goal with |- ?G => let G' := eval unfold T_UNW, T_QC, T_PC, PC_SZ in G in change_no_check G' end); lia | unfold T_UNW, T_QC, T_PC, PC_SZ in *; lia | hoff NHrt].
    assert (K_thr : rdn ASEGS Mr (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tback. }
    assert (K_T0 : rdn ASEGS Mr (Z_to_bv 64 T) 8 = Some (LE8 (Z_to_bv 64 CTX))) by thr_cell Hd M NHrt Tctx.
    assert (K_tid : rdn ASEGS Mr (at_ (Z_to_bv 64 CTX) 8) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 CTX) 8) with (Z_to_bv 64 (CTX + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Ttid. }
    assert (K_unw : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 3168) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 3168) with (Z_to_bv 64 (T + T_UNW)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_UNW in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tunw. }
    assert (K_sw : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 40) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 40) with (Z_to_bv 64 (T + 40)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tsw. }
    assert (K_top : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 8) 8 = Some (LE8 (Z_to_bv 64 (bt_stack_top bt)))).
    { replace (at_ (Z_to_bv 64 T) 8) with (Z_to_bv 64 (T + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Ttop. }
    assert (K_bot : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 16) 8 = Some (LE8 (Z_to_bv 64 (bt_stack_bottom bt)))).
    { replace (at_ (Z_to_bv 64 T) 16) with (Z_to_bv 64 (T + 16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tbot. }
    destruct SCELLS as (CELL_ipg & CELL_gnm & CELL_nm & CELL_pa & CELL_pab & SCREST).
    assert (K_ipg : rdn ASEGS Mr (Z_to_bv 64 (0x103f18 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096))) by konst Hd M R1 NHs CELL_ipg.
    assert (K_gnm : rdn ASEGS Mr (Z_to_bv 64 0xff258) 8 = Some (LE8 (Z_to_bv 64 0x1011e8))) by konst Hd M R1 NHs CELL_gnm.
    assert (K_nm : rdn ASEGS Mr (Z_to_bv 64 0x1011e8) 8 = Some (LE8 (Z_to_bv 64 0x1a2c0))) by konst Hd M R1 NHs CELL_nm.
    (* [comment removed for export] *)
    assert (SOKstk : store_ok ASEGS Mr (at_ S (-3584)) 3584 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. apply CPstk. cbn in Hx. lia. }
    assert (SOKT : store_ok ASEGS Mr (Z_to_bv 64 T) 4096 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ TW); wd_ulia_c. }
    assert (FPCr : fpc Mr (U (getr R 8)) (U S) DMAX).
    { rewrite CP2. apply (fpc_kept_gen M _ _ _ FPC Mr). destruct (fpc_shape _ _ _ _ FPC) as [ST|FR]; [left; exact ST | right].
      intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. apply NHs; unfold PTRHI in *; lia. }
    (* [comment removed for export] *)
    assert (En : getr R 10 = Z_to_bv 64 n) by (rewrite <- HR10; symmetry; apply Z_to_bv_bv_unsigned).
    destruct (run_mS_pre Mr (seg_rom ASEGS) R S ra0 tp (Z_to_bv 64 TSDP) (Z_to_bv 64 PGP) (Z_to_bv 64 (bt_stack_top bt)) (Z_to_bv 64 (bt_stack_bottom bt))
                (Z_to_bv 64 0x1a2c0) T CTX n DMAX eq_refl eq_refl eq_refl En)
      as (r5 & MP & sz & bsz & x18 & x19 & URUN).
    all: try assumption.
    all: try (wd_ulia_c).
    all: try (rewrite CP4; wd_ulia_c).
    all: try (lazymatch goal with |- _ \/ _ => rewrite ?CP2; unfold hide in *; unfold PG in *; lia end).
    all: try (rewrite CP2; split; [lia|]; split; [lia | apply mod4096_mod8s; exact TPG]).
    all: try (lazymatch goal with |- _ /\ _ => rewrite ?CP2; unfold hide in *; unfold PG in *; lia end).
    all: let k := numgoals in guard k = 1.
    clear K_mcs K_gcf K_fum K_inited K_kif K_key K_tsdp K_tctx K_rss K_lmag K_tbl2 K_t16 K_t2048 K_minrz K_maxrz K_maxsz K_gnm K_nm.
    cbn zeta in URUN.
    destruct URUN as (RUN & PRL & A1 & A21 & A10 & A11 & B3 & B4 & A26 & A27
                      & SZ1 & SZ2 & FOOTP & GRP & Psz4 & Psz8 & Lsz & Ptr & Pslots).
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (rewrite CP2; lia).
    pose proof (msf_outside Mr MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm FOOTP) as MFO.
    pose proof (msf_grows Mr MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GRP) as MFG.
    pose proof (msf_slotsA MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm) as MFS.
    pose proof (msf_rd_above MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm) as MFR.
    pose proof (msf_cb_slots MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm) as MFC.
    pose proof (msf_la_slots MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm) as MFL.
    set (MA := ma_A MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) in *.
    set (MF := ms_pre_mem S n MA) in *.
    clearbody MF. clear MA.
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end). replace (Z_to_bv 64 (ia_malloc asan_addrs)) with (Z_to_bv 64 0x6e4cc : word) by (apply bv_eq; reflexivity).
    replace (0x82004%bv : word) with (Z_to_bv 64 0x82004 : word) in RUN by (apply bv_eq; reflexivity).
    apply (katsD_msteps_acct ASEGS Hd (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x6e4cc) M (seg_rom ASEGS)) (@mkst fx r5 (Z_to_bv 64 0x82004) MF (seg_rom ASEGS)) mdl);
      [apply lazy_cover_HID | exact Bw1 | exact Bw2 | exact HH | rewrite restrict_mkst_s; exact RUN |].
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x6e4cc) M (seg_rom ASEGS))) with M by reflexivity.
    set (M1 := munrestrict Hd M MF).
    (* [comment removed for export] *)
    assert (VISstk : forall a : word, U S - 3584 <= U a < U S -> M1 a = MF a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply munrestrict_off. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply NHs; [pose proof (u64_range a); lia | left; rewrite CP2 in Ha; lia]. }
    assert (OUT1 : forall a : word, M1 a <> M a -> U S - 2416 <= U a < U S).
    { intros a NE. unfold M1, munrestrict in NE. destruct (Hd a) eqn:Eh; [exfalso; exact (NE eq_refl)|].
      assert (EMr : Mr a = M a) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); apply mrestrict_off; exact Eh).
      destruct (Z_lt_le_dec (U a) (U S - 2416)) as [L|L]; [exfalso; apply NE; rewrite <- EMr; apply MFO; left; exact L|].
      destruct (Z_lt_le_dec (U a) (U S)) as [L2|L2]; [lia | exfalso; apply NE; rewrite <- EMr; apply MFO; right; exact L2]. }
    assert (GRin : mem_grows M M1).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1, munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:Ex; [exact Hx|].
      apply MFG. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off by exact Ex. exact Hx. }
    assert (M1def : forall a : word, M1 a <> M a -> M1 a <> None).
    { intros a NE. destruct (M1 a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (M a) eqn:E2; [|reflexivity].
      exfalso. assert (X : M a <> None) by (rewrite E2; discriminate). apply GRin in X. rewrite E1 in X. exact (X eq_refl). }
    assert (STK1 : forall a : word, U S - 3584 <= U a < U S -> M1 a <> None /\ store_ok ASEGS M1 a 1%nat = true).
    { intros a Ha. split.
      - apply GRin. apply store_ok1_heap; [lia|]. apply CPstk. rewrite <- CP2. lia.
      - eapply store_ok_mono; [exact GRin|]. apply CPstk. rewrite <- CP2. lia. }
    assert (RX1 : RepX bt (fun _ : Z => False) st Lc FF M1 mdl1).
    { apply (repx_frame_step bt (fun _ : Z => False) st Lc FF M M1 mdl mdl1 W).
      - exists M. split; [exact RP | intros a NE; exfalso; exact (NE eq_refl)].
      - intros a NE. split; [| exact (M1def a NE)]. intros RCa.
        pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) W RCa) as LT. pose proof (OUT1 a NE) as O. rewrite CP2 in O. lia.
      - exact MI1.
      - exact SBM1. }
    (* [comment removed for export] *)
    assert (RD1 : forall (k : Z) (w : nat) (bs : list byte), -3584 <= k -> k + Z.of_nat w <= 0 -> rdn ASEGS MF (at_ S k) w = Some bs -> rdn ASEGS M1 (at_ S k) w = Some bs).
    { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply VISstk. lia. }
    assert (FA1 : forall (k0 : Z) (v : word), In (k0, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
              rdn ASEGS M1 (at_ S k0) 8 = Some (LE8 v)).
    { intros k0 v Hin. pose proof (ma_slotsA_range S n x18 x19 _ _ _ _ _ _ k0 v Hin) as [Hk1 Hk2].
      apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. exact (MFS k0 v Hin). }
    assert (FI1 : forall (k0 : Z) (v : word),
              In (k0, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
              rdn ASEGS M1 (at_ S k0) 8 = Some (LE8 v)).
    { intros k0 v Hin.
      assert (Hk : -56 <= k0 /\ k0 + 8 <= 0) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. apply MFR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (Pslots k0 v Hin)]. }
    assert (FS41 : rdn ASEGS M1 (at_ S (-2120)) 4 = Some (LE4 sz)) by (apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]; apply MFR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Psz4]).
    assert (FS81 : rdn ASEGS M1 (at_ S (-2120)) 8 = Some bsz) by (apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]; apply MFR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Psz8]).
    assert (FTR1 : rdn ASEGS M1 (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))) by (apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]; apply MFR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Ptr]).
    assert (FC1 : forall (o : Z) (v : word),
              In (o, v) [(-8, Z_to_bv 64 0x4bdc4); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048)]%Z ->
              rdn ASEGS M1 (at_ (at_ S (-2272)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -48 <= o <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (MFC o v Hin). }
    assert (FL1 : forall (o : Z) (v : word),
              In (o, v) [(-8, Z_to_bv 64 0x50324); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048);
                         (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x103f18); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)]%Z ->
              rdn ASEGS M1 (at_ (at_ S (-2320)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -88 <= o <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (MFL o v Hin). }

    (* [comment removed for export] *)
    set (spL := at_ S (-2320)). set (spM := at_ (at_ S (-2320)) (-96)).
    set (szW := Z_to_bv 64 (la_msz (sec_needed n)) : word). set (nmW := Z_to_bv 64 0x1a2c0 : word).
    assert (Hn1 : 64512 < n) by lia.
    pose proof BD as ((BP0 & BP1) & BC1 & (BK0 & BK1)).
    assert (HnG : 64513 <= n <= GBUDGET) by (unfold GBUDGET, MBLK in *; lia).
    assert (MSZ : la_msz (sec_needed n) = sec_map_size n) by apply la_msz_sec.
    destruct (sec_msz_bnd n Hn1) as [MZ1 MZ2].
    assert (Usz : U szW = sec_map_size n) by ((lazymatch goal with |- ?G => let G' := eval unfold szW in G in change_no_check G' end); rewrite MSZ, u_Z2bv by lia; reflexivity).
    assert (UspM : U spM = U S - 2416) by ((lazymatch goal with |- ?G => let G' := eval unfold spM in G in change_no_check G' end); rewrite at_at, at_u by lia; lia).
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl1 & _ & _ & _ & Eeg1).
    pose proof PRL as (P2 & P8 & P9 & P18 & P19 & P24).
    assert (IMG1 : forall (z : Z) (k : nat) v, In (z, k, v) (bt_consts bt) -> AIMGLO <= z -> z + Z.of_nat k <= AIMGHI ->
              rdn ASEGS M1 (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Hin Hz Hk. pose proof (const_cell bt M _ _ _ R1 Hin) as Cc. unfold cellZ, cellN in Cc. rewrite <- Cc.
      apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
      destruct (decide (M1 x = M x)) as [E|NE]; [exact E|]. pose proof (OUT1 x NE). lia. }
    assert (NHw : forall x : word, (CEIL <= U x \/ (AIMGLO <= U x /\ U x < AIMGHI)) -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | exact Hx]. }
    pose proof (sec_pre_budget bt st Lc FF M mdl B C K n 0 RP W BD Hn1 HB HK ltac:(clear; lia)) as BUD0.   (* [comment removed for export] *)
    pose proof (sec_shs_bnd 0 n ltac:(clear; lia) Hn1) as BUDH.
    assert (NOH : forall z, ~ holes bt st z) by exact (sec_no_holes bt h n st HPH HO Hn1).
    assert (GFACTS : forall mdlm (a : word), same_but_materialized mdl1 mdlm -> grant_ok (Z_to_bv 64 0) mdlm a (sec_map_size n) = true ->
              same_but_materialized mdl mdlm /\ m_vmmaps mdlm = m_vmmaps mdl /\ m_vm_lazy mdlm = m_vm_lazy mdl
              /\ dyn_ok (bt_ia bt) (U a) (U a + sec_map_size n) /\ U a mod PG = 0
              /\ (forall lo hi, In (lo, hi) (all_ranges bt st) -> U a + sec_map_size n <= lo \/ hi <= U a)
              /\ AIMGHI <= U a /\ U a + sec_map_size n <= CEIL).
    { intros mdlm a SBMm G. pose proof (same_but_materialized_trans _ _ _ SBM1 SBMm) as SBM0m.
      destruct (sbm_vmmaps _ _ SBM0m) as [EVm ELm].
      destruct (grant_ok_facts bt st Lc FF M mdl mdlm (2 ^ 20) (2 ^ 28) W RP BOOTG EVm (Z_to_bv 64 0) a (sec_map_size n) h ltac:(lia) MZ1
                  (or_introl NOH) G) as (DY & AL & AP).
      split; [exact SBM0m|]. split; [exact EVm|]. split; [exact ELm|]. split; [exact DY|]. split; [exact AL|]. split; [exact AP|].
      destruct DY as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite BT_ia in Y4. cbn [ia_img_lo ia_img_hi asan_addrs] in Y4. split; [lia | exact Y3]. }
    destruct PCELLS as (_ & _ & _ & CELL_dpm & CELL_lim).
    replace (Z_to_bv 64 0x82004) with (0x82004%bv : word) by (apply bv_eq; reflexivity).
    apply (mmapordie_katsD Hd (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st) r5 M1 (seg_rom ASEGS) mdl1 spM (Z_to_bv 64 0x50610)
             (Z_to_bv 64 0x1041c8) (Z_to_bv 64 (0x103f18 + 64)) szW (Z_to_bv 64 (sec_needed n)) (getr r5 20) (Z_to_bv 64 8) szW nmW PGP 0x1990a8 Qok Qf
             (fun mdlm a => grant_ok (Z_to_bv 64 0) mdlm a (sec_map_size n) = true) (fun mdlm a => mmap_model a szW mdlm)).
    - exact A1.
    - exact P2.
    - exact A10.
    - exact A11.
    - exact P8.
    - exact P9.
    - exact P18.
    - exact P19.
    - reflexivity.
    - exact A21.
    - rewrite UspM. lia.
    - apply ret_ok_lit; [lia | reflexivity].
    - rewrite Usz. split; [exact MZ1 | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold nmW in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
    - lia.
    - lia.
    - apply store_ok_bytes; [| rewrite at_u by (rewrite UspM; lia); rewrite UspM; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. intros x Hx. rewrite at_u in Hx by (rewrite UspM; lia). rewrite UspM in Hx. cbn in Hx.
      exact (proj2 (STK1 x ltac:(lia))).
    - exact (IMG1 _ _ _ CELL_pg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (IMG1 _ _ _ CELL_P ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (IMG1 _ _ _ CELL_gcf ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - change (Some [Z_to_bv 8 0]) with (Some (word_to_le_bytes 1 (Z_to_bv 64 0))). exact (IMG1 _ _ _ CELL_dpm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (IMG1 _ _ _ CELL_lim ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. left. rewrite UspM in Hx. lia.
    - rewrite Ehl1. exact HH.
    - rewrite Elz1. apply lazy_cover_HID.
    - exact Bw1.
    - exact MI1.
    - (* [comment removed for export] *) intros mdlm a SBMm G. destruct (GFACTS mdlm a SBMm G) as (_ & _ & _ & _ & _ & _ & GA & GC). rewrite Usz, UspM. lia.
    - (* [comment removed for export] *) intros mdlm rr SBMm MIm HLm B10 B11 B12 B13 B14 B15 Qok' Qf' KOK KKP.
      apply (node2_of_mmap_rw rr _ _ mdlm szW Qok' Qf' HLm B10 B11 B12 B13 B14 B15 ltac:(rewrite Usz; lia) ltac:(rewrite Usz; exact MZ1)).
      + rewrite Usz. apply (sec_grant_ex bt BOK BTOT st Lc FF M mdl mdlm n W RP (same_but_materialized_trans _ _ _ SBM1 SBMm) MIm KC HnG). lia.
      + intros a Ha. rewrite Usz in Ha. exact (KOK a Ha).
      + exact KKP.
    - (* [comment removed for export] *) intros mdlm a SBMm MIm G. destruct (GFACTS mdlm a SBMm G) as (SBM0m & EVm & ELm & _ & _ & _ & GA & GC).
      split; [rewrite mmap_model_halted; pose proof (same_but_materialized_frame mdl mdlm SBM0m) as F;
              destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _); rewrite HL; exact HH|].
      split; [rewrite mmap_model_lazy, ELm; apply lazy_cover_HID|].
      apply (plain_child_MInv mdl mdlm a szW MW EVm ELm ltac:(rewrite Usz; lia) (a_aa st) MIm). rewrite Usz. lia.
    - (* [comment removed for export] *)
      intros a r' mdlm mdl4 SBMm MIm G SBM4 MI4 MR.
      destruct (GFACTS mdlm a SBMm G) as (SBM0m & EVm & ELm & DY & AL & AP & GA & GC).
      pose proof (u64_range a) as Har.
      destruct MR as (Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & AGm).
      assert (END64 : U a + U szW <= 2 ^ 64) by (rewrite Usz; lia).
      pose proof (plain_child_ledger mdl mdlm mdl4 a szW MW EVm ELm END64 SBM4) as (LV & LN & LL & LR & LB & LSB & LMB & LIS & LLIM & LEG & LMW).
      assert (HL4 : m_halted mdl4 = None).
      { pose proof (same_but_materialized_frame _ _ SBM4) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hh4 & _). rewrite Hh4, mmap_model_halted.
        pose proof (same_but_materialized_frame mdl mdlm SBM0m) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhm & _). rewrite Hhm. exact HH. }
      match goal with |- katwD _ (mkCfg (mkst _ _ ?m _) _) _ _ => set (MG := m) end.
      assert (CEILS : CEIL + 3584 <= U S) by (rewrite CP2; lia).
      assert (MGout : forall x : word, (U x < U S - 2736 \/ U S - 2416 <= U x) -> ~ (U a <= U x < U a + sec_map_size n) -> MG x = M1 x).
      { intros x Hx Hna. (lazymatch goal with |- ?G => let G' := eval unfold MG in G in change_no_check G' end).
        rewrite wbytes_outside by (wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by (rewrite UspM; lia); rewrite UspM; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
        rewrite zfill_out by (rewrite Usz; lia). apply mod_m1_outside; [rewrite UspM; lia | rewrite UspM; lia]. }
      assert (MGgr : mem_grows M1 MG).
      { (lazymatch goal with |- ?G => let G' := eval unfold MG in G in change_no_check G' end). eapply mem_grows_trans; [| apply wbytes_grows]. eapply mem_grows_trans; [| apply zfill_grows_s]. apply mod_m1_grows. }
      assert (MGz : forall x : word, U a <= U x < U a + sec_map_size n -> MG x = Some (Z_to_bv 8 0)).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MG in G in change_no_check G' end).
        rewrite wbytes_outside by (wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by (rewrite UspM; lia); rewrite UspM; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
        apply zfill_in_s. rewrite Usz. exact Hx. }
      assert (RDG : forall (k : Z) (w : nat) (bs : list byte), -2416 <= k -> k + Z.of_nat w <= 0 -> rdn ASEGS M1 (at_ S k) w = Some bs -> rdn ASEGS MG (at_ S k) w = Some bs).
      { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply MGout; lia. }
      assert (NCm : forall i : reg, ~ In i mod_clob -> getr r' i = getr r5 i) by (intros i Hi; exact (AGm i Hi)).
      Ltac ncm := (lazymatch goal with |- ?G => let G' := eval unfold mod_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X.
      apply CONT1.
      exists r', MG, mdl4, a. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold S.
      split; [reflexivity|].
      split. { (lazymatch goal with |- ?G => let G' := eval unfold chunk_child in G in change_no_check G' end). replace (Z_to_bv 64 (sec_map_size n)) with szW by ((lazymatch goal with |- ?G => let G' := eval unfold szW in G in change_no_check G' end); rewrite MSZ; reflexivity).
               repeat (split; [assumption|]). exact HL4. }
      split; [exact MI4|]. split; [exact DY|]. split; [exact AL|]. split; [exact AP|].
      split. { intros b0 n0 Hin. exact (grant_apart_maps0 bt st Lc FF M mdl mdlm (2 ^ 20) (2 ^ 28) (Z_to_bv 64 0) a (sec_map_size n) W RP EVm ltac:(lia) MZ1 G b0 n0 Hin). }
      split; [exact Q10|].
      split.
      { exists x18, x19, sz, bsz. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold S.
        split. { (lazymatch goal with |- ?G => let G' := eval unfold la_regs in G in change_no_check G' end). split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|].
                 split; [rewrite NCm by ncm; exact P19 | rewrite NCm by ncm; exact P24]. }
        split; [rewrite NCm by ncm; exact A21|].
        split; [rewrite NCm by ncm; exact B4|]. split; [rewrite NCm by ncm; exact B3|].
        split; [rewrite NCm by ncm; exact A26|]. split; [rewrite NCm by ncm; exact A27|].
        split. { intros k0 v Hin. pose proof (ma_slotsA_range S n x18 x19 _ _ _ _ _ _ k0 v Hin) as [Hk1 Hk2]. apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FA1 k0 v Hin)]. }
        split. { intros k0 v Hin.
                 assert (Hk : -56 <= k0 /\ k0 + 8 <= 0) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
                 apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FI1 k0 v Hin)]. }
        split; [apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FS41]|].
        split; [apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FS81]|].
        split; [exact Lsz|].
        split; [clear - SZ1 SZ2; change (Z.of_nat DMAX) with 6 in SZ2; lia|].
        split; [apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FTR1]|].
        split. { intros o v Hin.
                 assert (Ho : -48 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
                 rewrite at_at. apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FC1 o v Hin). }
        split. { intros o v Hin.
                 assert (Ho : -88 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
                 rewrite at_at. apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FL1 o v Hin). }
        intros x Hx. unfold MSTK_A in Hx. destruct (STK1 x ltac:(lia)) as [D1 D2]. split; [exact (MGgr x D1) | eapply store_ok_mono; [exact MGgr | exact D2]]. }
      split. { intros x NE. destruct (Z_lt_le_dec (U x) (U a)) as [L1|L1]; [| destruct (Z_lt_le_dec (U x) (U a + sec_map_size n)) as [L2|L2]; [right; lia|]].
               - left. destruct (Z_lt_le_dec (U x) (U S - 2736)) as [L3|L3]; [exfalso; apply NE; rewrite MGout by lia; destruct (decide (M1 x = M x)) as [E|NE1]; [exact E | pose proof (OUT1 x NE1); lia]|].
                 destruct (Z_lt_le_dec (U x) (U S)) as [L4|L4]; [lia|]. exfalso; apply NE; rewrite MGout by lia; destruct (decide (M1 x = M x)) as [E|NE1]; [exact E | pose proof (OUT1 x NE1); lia].
               - left. destruct (Z_lt_le_dec (U x) (U S - 2736)) as [L3|L3]; [exfalso; apply NE; rewrite MGout by lia; destruct (decide (M1 x = M x)) as [E|NE1]; [exact E | pose proof (OUT1 x NE1); lia]|].
                 destruct (Z_lt_le_dec (U x) (U S)) as [L4|L4]; [lia|]. exfalso; apply NE; rewrite MGout by lia; destruct (decide (M1 x = M x)) as [E|NE1]; [exact E | pose proof (OUT1 x NE1); lia]. }
      split; [exact MGz|].
      split; [eapply mem_grows_trans; [exact GRin | exact MGgr]|].
      apply (same_except_vm_trans mdl mdlm mdl4); [apply same_but_materialized_except_vm; exact SBM0m|].
      apply (same_except_vm_trans mdlm (mmap_model a szW mdlm) mdl4); [apply mmap_except_vm | apply same_but_materialized_except_vm; exact SBM4].
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBMm MIm SBM4 MI4 MR.
      pose proof (same_but_materialized_trans _ _ _ SBM1 SBMm) as SBM0m.
      pose proof (same_but_materialized_trans _ _ _ SBM0m SBM4) as SBM04.
      destruct MR as (Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & AGm).
      assert (HL4 : m_halted mdl4 = None).
      { pose proof (same_but_materialized_frame mdl mdl4 SBM04) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hh4 & _). rewrite Hh4. exact HH. }
      match goal with |- katD _ (mkCfg (mkst _ _ ?m _) _) _ => set (MN := m) end.
      assert (CEILS : CEIL + 3584 <= U S) by (rewrite CP2; lia).
      assert (MNout : forall x : word, (U x < U S - 2736 \/ U S - 2416 <= U x) -> MN x = M1 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MN in G in change_no_check G' end).
        rewrite !wbytes_outside by (wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by (rewrite UspM; lia); rewrite UspM; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
        apply mod_m1_outside; [rewrite UspM; lia | rewrite UspM; lia]. }
      assert (MNgr : mem_grows M1 MN).
      { (lazymatch goal with |- ?G => let G' := eval unfold MN in G in change_no_check G' end). eapply mem_grows_trans; [| apply wbytes_grows]. eapply mem_grows_trans; [| apply wbytes_grows]. apply mod_m1_grows. }
      assert (RDN : forall (k : Z) (w : nat) (bs : list byte), -2416 <= k -> k + Z.of_nat w <= 0 -> rdn ASEGS M1 (at_ S k) w = Some bs -> rdn ASEGS MN (at_ S k) w = Some bs).
      { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply MNout; lia. }
      assert (NCm : forall i : reg, ~ In i mod_clob -> getr r' i = getr r5 i) by (intros i Hi; exact (AGm i Hi)).
      assert (RXN : RepX bt (fun _ : Z => False) st Lc FF MN mdl4).
      { apply (repx_frame_step bt (fun _ : Z => False) st Lc FF M1 MN mdl1 mdl4 W RX1).
        - intros x NE. split.
          + intros RCx. pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U x) W RCx) as LT.
            destruct (Z_lt_le_dec (U x) (U S - 2736)) as [L3|L3]; [apply NE; apply MNout; lia|].
            destruct (Z_lt_le_dec (U x) (U S - 2416)) as [L4|L4]; [lia | apply NE; apply MNout; lia].
          + destruct (MN x) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (M1 x) eqn:E2; [|reflexivity].
            exfalso. assert (X : M1 x <> None) by (rewrite E2; discriminate). apply MNgr in X. rewrite E1 in X. exact (X eq_refl).
        - exact MI4.
        - exact (same_but_materialized_trans _ _ _ SBMm SBM4). }
      destruct RXN as (M0n & RPn & DXn).
      assert (EMn : MN = M0n).
      { apply functional_extensionality. intros x. destruct (decide (MN x = M0n x)) as [E|NE]; [exact E | destruct (DXn x NE) as [[] _]]. }
      subst M0n.
      apply CONT0.
      exists r', MN, mdl4. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold S.
      split; [reflexivity|]. split; [exact HL4|]. split; [exact (model_ivs_wf_sbm mdl mdl4 SBM04 MW)|]. split; [exact RPn|].
      split; [exact Q10|].
      split.
      { exists x18, x19, sz, bsz. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold S.
        split. { (lazymatch goal with |- ?G => let G' := eval unfold la_regs in G in change_no_check G' end). split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|].
                 split; [rewrite NCm by ncm; exact P19 | rewrite NCm by ncm; exact P24]. }
        split; [rewrite NCm by ncm; exact A21|].
        split; [rewrite NCm by ncm; exact B4|]. split; [rewrite NCm by ncm; exact B3|].
        split; [rewrite NCm by ncm; exact A26|]. split; [rewrite NCm by ncm; exact A27|].
        split. { intros k0 v Hin. pose proof (ma_slotsA_range S n x18 x19 _ _ _ _ _ _ k0 v Hin) as [Hk1 Hk2]. apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FA1 k0 v Hin)]. }
        split. { intros k0 v Hin.
                 assert (Hk : -56 <= k0 /\ k0 + 8 <= 0) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
                 apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FI1 k0 v Hin)]. }
        split; [apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FS41]|].
        split; [apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FS81]|].
        split; [exact Lsz|].
        split; [clear - SZ1 SZ2; change (Z.of_nat DMAX) with 6 in SZ2; lia|].
        split; [apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FTR1]|].
        split. { intros o v Hin.
                 assert (Ho : -48 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
                 rewrite at_at. apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FC1 o v Hin). }
        split. { intros o v Hin.
                 assert (Ho : -88 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
                 rewrite at_at. apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FL1 o v Hin). }
        intros x Hx. unfold MSTK_A in Hx. destruct (STK1 x ltac:(lia)) as [D1 D2]. split; [exact (MNgr x D1) | eapply store_ok_mono; [exact MNgr | exact D2]]. }
      split. { intros x NE. destruct (Z_lt_le_dec (U x) (U S - 2736)) as [L3|L3]; [exfalso; apply NE; rewrite MNout by lia; destruct (decide (M1 x = M x)) as [E|NE1]; [exact E | pose proof (OUT1 x NE1); lia]|].
               destruct (Z_lt_le_dec (U x) (U S)) as [L4|L4]; [lia|]. exfalso; apply NE; rewrite MNout by lia; destruct (decide (M1 x = M x)) as [E|NE1]; [exact E | pose proof (OUT1 x NE1); lia]. }
      split; [apply same_but_materialized_except_vm; exact SBM04|].
      intros z Hz. exact (lazy_kept_sbm bt Lc FF mdl mdl4 SBM04 z Hz).
  Qed.
End TOPSA.
End WithCeil.
