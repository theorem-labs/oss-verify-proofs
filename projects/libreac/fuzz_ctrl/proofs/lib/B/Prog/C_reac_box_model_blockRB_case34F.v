(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 712 of its 727 lines of code are new or changed and 233 lines of the source are left out. *)
(* GENERATED - do not edit.  C_reac_box_model_blockRB_case34F.v is the re-based copy of lib/B/Prog/reac_box_model_block_case34F.v at 20372bbcc3a
   (source sha256 85c0716a4509309c881445024666ae2bd624d66abab79adca332ffe098b9ea61) by gen_rb_modelblock.py
   (its sha256 is cited in the commit that adds this file); the substitutions are listed there.  Dropped here: nothing. *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
(* The footprint twin of C_reac_box_model_blockRB_case34.v (image B, asan-ubsan; route 2): cases b = 3 and b = 4 of
   reac_box_model_block as ExecF.evtF runs under the footprint RNG, by the plain file's scripts over StepF's step.
   The pure lemmas of the plain file (c34_chk, c34_sub_post, c34_geo, c34_out, c34_addr, c34_mod8) are reused from
   it; this file restates only the two case walks, whose statements mention `evt`. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  C_reac_box_model_blockRB C_reac_box_model_blockRB_case34 C_reac_box_model_blockRBF.
(* Last: StepF's step / if_false / mem_after_store (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_model_block_c_on reac_box_model_block_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c_on asan_stack_malloc_cF_on asan_memset_c_on asan_memset_cF_on
  asan_memcpy_c_on asan_memcpy_cF_on name_field_c_on sh_word_on C_reac_box_model_blockOnHB
  C_reac_box_model_blockOnHD.
Import ListNotations.
Open Scope Z_scope.

(* Local copy of C_reac_box_model_blockRB.v:228's store hook: that file made it Local (a Theorem Labs lane; generator owner a Theorem Labs lane stopped, a Theorem Labs lane audits). *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* The two hooks of C_reac_box_model_blockRBF.v (Local there, so restated here verbatim). *)
Ltac mbF_fix_lit_store :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

Ltac mbF_store_opt :=
  try mbF_fix_lit_store;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= mbF_store_opt.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= mbF_acc_hint.

Section Case34F.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint).
  Hypothesis HSM : asan_stack_malloc_0_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw_on (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
  Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
    (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rb : 0 <= b < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis HP : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
    (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o).
  Hypothesis HN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    name_ok nb /\ bytes_at rsegs m (rname row) nb /\
    (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
    (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o).
  Hypothesis HO : o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
    (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
  Hypothesis AP : p <> 0 -> addressable m p 296.
  Hypothesis ANB : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    addressable m (rname row) (Z.of_nat (length nb)).
  Hypothesis AO : o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).
  Hypothesis AJ1 : b = 1 -> addressable m JOIN_0014 32.
  Hypothesis AJ2 : b = 2 -> addressable m JOIN_0013 32.
  Hypothesis NDJ : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS).


  Hypothesis HMS : asan_memset_contract_F_on.
  Hypothesis HMC : asan_memcpy_contract_F_on.
  Hypothesis HBD : build_dt1_single_contract_F_on.
  Hypothesis HDH : dt1_head_contract_F_on.
  Hypothesis HNF : name_field_contract_F_on.

  (* The frame release at 0x86e14 (rel_stmt of the interface pin); its proof is in the body file. *)
  Hypothesis Hrel : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
       (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
  FK FS A fr f spc j n w56 ->
  ret = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
  BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS
     (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) fr w56 mc ->
  (if (p =? 0) || (o =? 0) then True else bytes_at rsegs mc o (synth row b nb)) ->
  evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
    (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
            (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86e14) fc None mc (seg_rom rsegs)).

  (* The footprint of the run (C_reac_box_model_blockRBF.v); `mbF_open HRNG` unpacks it. *)
  Hypothesis HRNG : mbF_rng RNG m sp tp p b o FS row nb.

  (* The byte at a, writable in m, is writable now. *)
  Ltac c34_wv :=
    let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii;
    first [ apply (stk_wv m _ _ _ ST0); lia
          | match goal with
            | FW : forall i, 0 <= i < 64 -> wview rsegs m (wa (?frr + i)) <> None |- wview _ _ (wa ?x) <> None =>
                replace x with (frr + (x - frr)) by lia; apply FW; lia
            end
          | match goal with
            | SW : forall i, 0 <= i < 8 -> wview rsegs m (wa (?ss + i)) <> None |- wview _ _ (wa ?x) <> None =>
                replace x with (ss + (x - ss)) by lia; apply SW; lia
            end ].

  Ltac c34_wst a n :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) n = true)
          by (eapply wv_store_ok; [ c34_wv | eassumption | lia | lia ])
    end.

  (* Read back the bytes a store just wrote. *)
  Ltac c34_keep a :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
        let H := fresh "D" in
        assert (H : bytes_at rsegs (write_to_mem mm (wa a) bs) a bs)
          by (apply bytes_at_write_same; [lia | simpl_sizes; lia])
    end.

  (* The facts a checked 2-byte load of the row field at p + kz needs (kn is the same offset as a nat). *)
  Ltac c34_facts CA LR HK kz kn ADp SHk RXk RDk :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (ADp : addressable mm p 296) by
          (apply (CA mm p 296);
           [ eassumption | eassumption
           | exact HK
           | unfold Wf, shadow_addr; cbn [app]; eassumption
           | eassumption | assumption ]);
        assert (SHk : exists kk : byte, ov_read_bytes rsegs mm (wa ((p + kz) / 8 + off)) 1 = Some [kk]
                        /\ (bv_signed kk = 0 \/ (p + kz) mod 8 + (2 - 1) < bv_signed kk)
                        /\ -128 <= bv_signed kk < 128)
          by (apply (c34_chk off Hoff mm p 296 kz 2 (p + kz) ADp);
              [ lia | lia
              | lia
              | apply c34_mod8; [assumption | lia]
              | lia ]);
        assert (RXk : 0 <= p + kz < 2^64) by lia;
        pose proof (rs_rd2 rsegs mm p row kn ltac:(eassumption) ltac:(clear -LR; lia)) as RDk;
        change (Z.of_nat kn) with kz in RDk
    end.

  Lemma c34_case3F : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    b = 3 -> p <> 0 -> o <> 0 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 (zeros 32)] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86a08) fc None mc (seg_rom rsegs)).
  Proof using All.
    mbF_open HRNG.
    intros fr f spc j n w56 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
      Hb Hp0 Ho0 HK HB HOC.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    destruct (c34_geo sp tp m p b o FS off A row nb ob Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HP HO
      fr f spc j n w56 Hp0 Ho0 HK) as
      (GA32 & GAlo & GFS0 & GFSsz & Gn & Gj & GFR8 & GFRlo & GFRhi & Gspb & GDSP &
       GOFR & GPFR & GOFS & GPFS & GOFL & GPFL).
    destruct (fk_facts sp tp m p o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 fr f spc j n w56 HK)
      as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SWv & SH1 & SH2).
    pose proof (c34_sub_post sp m p b o FS A row nb ob HA HS16 Rp Rb Ro HP HO fr f spc j n w56 Ho0 HK) as SUB.
    destruct (HP Hp0) as (Hp8 & Lrow & HRm & HPw & HPo).
    destruct (AO Ho0) as (AOm & AOe & AOrt).
    destruct (HO Ho0) as (_ & HOw & _).
    pose proof (AP Hp0) as APm.
    pose proof (br_ac sp tp m p b o FS row nb ob AC0 HHM HAE FP0 Rp Rb Ro HP HO AO) as BRAC.
    pose proof (c34_addr sp tp m p b o FS off A row nb ob Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HP HO AO
                    fr f spc j n w56) as CADDR.
    destruct HB as (MU & WM & RM & MI & SV & (hh & HH) & F56).
    unfold Wf in MU. cbn [app] in MU. unfold shadow_addr in MU.
    (* PERF: every lia below names the few facts it needs; the section's implications never reach zify. *)
    assert (LHM : 17594333495296 <= bv_unsigned sp - 4272) by (clear -HHM; unfold HIGHMEM_BEG in HHM; lia).
    assert (LAE : bv_unsigned sp <= 140737488355328) by (clear -HAE; unfold APPMEM_END in HAE; lia).
    assert (APe : p + 296 <= 140737488355328)
      by (clear -APm; destruct APm as (_ & _ & He & _); unfold APPMEM_END in He; lia).
    assert (AOq : o + 32 <= 140737488355328)
      by (clear -AOm; destruct AOm as (_ & _ & He & _); unfold APPMEM_END in He; lia).
    assert (LP : p + 296 <= 2147450880 \/ 17594333495296 <= p)
      by (clear -APm sp m; apply (app_range sp p 296);
          [lia | intros i Hi; apply (acl_app_in m p 296); [exact APm | lia]]).
    assert (LO : o + 32 <= 2147450880 \/ 17594333495296 <= o)
      by (clear -AOm sp m; apply (app_range sp o 32);
          [lia | intros i Hi; apply (acl_app_in m o 32); [exact AOm | lia]]).
    assert (LFS : FS + 8 <= 2147450880 \/ 17594333495296 <= FS).
    { clear -FP0 GFS0.
      pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & PL & _). pose proof PL as (_ & _ & _ & PL4 & _).
      unfold FS_SIZE in PL4.
      pose proof (PL4 FS ltac:(lia)) as H1. pose proof (PL4 (FS + 7) ltac:(lia)) as H2.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. clear -H1 H2. lia. }
    assert (OUTP : forall x, p <= x < p + 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x)
      by (intros x Hx;
          exact (c34_out sp o FS off fr j n p 296 x SH1 SH2 Hoff
                   ltac:(replace x with (p + (x - p)) by (clear -Hx; lia);
                         apply (acl_app_in m p 296); [exact APm | clear -Hx; lia])
                   Hx ltac:(clear -HPw; lia) ltac:(clear -GPFS; lia) ltac:(clear -GPFL; lia)
                   ltac:(clear -GPFR; lia) ltac:(clear -HPo Ho0; lia) ltac:(clear -Gn; lia))).
    assert (HRc : bytes_at rsegs mc p row).
    { apply (fl_bytes (Wf sp FS fr j n ++ [(o, o + 32)]) m mc p row HRm);
        [unfold Wf, shadow_addr; cbn [app]; exact MU|].
      intros x Hx. rewrite Lrow in Hx. apply OUTP. clear -Hx; lia. }
    assert (APc : addressable mc p 296)
      by (apply (CADDR mc p 296 Hp0 Ho0 HK);
          [unfold Wf, shadow_addr; cbn [app]; exact MU | exact APm | clear -GPFR; lia]).
    assert (RX : 0 <= p + 266 < 2^64) by (clear -Rp APe; lia).
    pose proof (c34_chk off Hoff mc p 296 266 2 (p + 266) APc ltac:(clear -Hp8; lia) ltac:(clear -Hp8; lia)
      ltac:(clear -Hp8; lia) ltac:(clear -Hp8; Z.div_mod_to_equations; lia) ltac:(clear -Hp8; lia)) as SH.
    pose proof (rs_rd2 rsegs mc p row 266 HRc ltac:(clear -Lrow; lia)) as RD.
    change (Z.of_nat 266) with 266 in RD.
    pose proof (rs_rw16_range row 266) as Rw.
    (* the footprint facts of the walk: the row, the output block and the frame [fr, fr + 64), which lies in the
       window (n = 0) or in the class-0 frames (n = 1) *)
    destruct (RROW Hp0) as (RROWr & RROWc & RROWs & RROWk).
    destruct (ROUT Hp0 Ho0) as (ROUTr & ROUTc & ROUTs & ROUTk).
    assert (FRM : rng RNG fr 64 /\ shcov RNG fr 64 /\ shkov RNG fr 64).
    { clear -HK RWIN SWIN KWIN RFR SFR KFR GAlo.
      destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
      - subst fr. split; [eapply rng_sub; [exact RWIN | lia | lia]|].
        split; [eapply shcov_sub; [exact SWIN | lia | lia] | eapply shkov_sub; [exact KWIN | lia | lia]].
      - change (fs_M 0) with 16384 in Hj.
        assert (Efrv : fr = FS + 36864 + j * 64) by (rewrite Efr; unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
        split; [eapply rng_sub; [exact RFR | lia | lia]|].
        split; [eapply shcov_sub; [exact SFR | lia | lia] | eapply shkov_sub; [exact KFR | lia | lia]]. }
    destruct FRM as (RFRM & SFRM & KFRM).
    pose proof (mbF_blk RNG fr 64 fr SFRM FR8 (Z.le_refl fr) (Z.le_refl (fr + 64))) as BLK.
    (* route (C), HD site 5: every word cover inside the frame [fr, fr + 64) lies in the run's region R (the
       frame is the real-stack frame in the window or the class-0 frame in the class-0 block: mbHD_R_fr); the
       build_dt1_single call below takes the cover of its source, the digits at fr + 32, from here *)
    assert (SRfr : forall q k a, 0 <= k -> fr <= q -> q + k <= fr + 64 -> sh_word_on q k a ->
                     reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb a).
    { assert (F64 : FS mod 64 = 0).
      { clear -FP0. pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & PL & _).
        pose proof PL as (_ & PL2 & _). clear -PL2. Z.div_mod_to_equations. lia. }
      intros q k a Hk Hq1 Hq2 Ha.
      apply (mbHD_R_fr (bv_unsigned sp) FS p b o row nb A fr j q k a F64 GAlo);
        [| exact Hk | exact Hq1 | exact Hq2 | exact Ha].
      clear -HK. destruct HK as [(_ & Efr & _) | (Hj & Efr & _)]; [left; exact Efr | right].
      change (fs_M 0%nat) with 16384 in Hj. split; [exact Hj | exact Efr]. }
    (* PERF: the walk runs with a small context; every lia below sees only linear facts and six separations. *)
    clear - SRfr Hb Hp0 Ho0 HK MU WM RM MI SV HH F56 HOC HRc SH RD RX Rw Hp8 FR8 Lrow SH1 SH2 Hoff
      GAlo GFRlo GFRhi GFS0 GFSsz Gspb GDSP GOFR GPFR GOFS GPFS LP LO LFS FRA LHM LAE
      Rp Ro APe AOq AOe AOrt FW FAP SWv ST0 SR0 BRAC CADDR SUB HBD Hrel Rsp APm AOm HOw HPw
      RIMG RWIN KWIN RBY RROWr RROWc ROUTr ROUTk RFRM KFRM BLK.
    (* 0x86a08: p is 8-aligned *)
    step.
    rewrite (unsigned_lit p) by lia. rewrite rc_land7, Hp8.
    step. nf.
    step.
    try (rewrite (unsigned_lit p) by lia).
    chk_core (p + 266) RX (Z_to_bv 5 12) SH pre_sr add1.
    step. try rewrite rs_zx16.
    clear HRc.
    pose proof (C34Box _ (conj GDSP (conj GOFS (conj GPFS (conj HOw (conj HPw (conj AOrt (conj GPFR LP)))))))) as BOX.
    clear GDSP GOFS GPFS HOw HPw AOrt GPFR LP.
    step. step.
    try (rewrite (unsigned_lit (rw16 row 266)) by lia).
    try (rewrite Z.shiftr_div_pow2 by lia).
    try (change (2 ^ 4) with 16).
    step.
    c34_wst (fr / 8 + off + 4) 1%nat.
    step.
    c34_keep (fr / 8 + off + 4).
    store_done.
    step.
    destruct (Z.leb_spec (rw16 row 266) 9999) as [V|V].
    - (* w <= 9999: the four digits at fr + 32, then build_dt1_single *)
      nt.
      do 7 step.
      c34_wst (fr + 32) 1%nat. step. c34_keep (fr + 32). store_done.
      step. nf.
      do 13 step.
      c34_wst (fr + 33) 1%nat. step. c34_keep (fr + 33). store_done.
      step. nf.
      do 12 step.
      c34_wst (fr + 34) 1%nat. step. c34_keep (fr + 34). store_done.
      step. nf.
      do 3 step.
      c34_wst (fr + 35) 1%nat. step. c34_keep (fr + 35). store_done.
      do 3 step.
      (* the four bytes read back as the digits of w *)
      match goal with
      | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (HD : bytes_at rsegs mm (fr + 32) (digits (rw16 row 266)));
          [ eapply bytes_at_ext;
            [ apply (c34_app2 _ (fr + 32) (fr + 33)); [eassumption | | simpl_sizes; lia];
              apply (c34_app2 _ (fr + 33) (fr + 34)); [eassumption | | simpl_sizes; lia];
              apply (c34_app2 _ (fr + 34) (fr + 35)); [eassumption | eassumption | simpl_sizes; lia]
            | unfold digits, le1; cbn [map app Z_to_le_bytes]; apply mb_l4; unfold bz;
              rs_brute_tac (rw16 row 266) ] | ]
      end.
      (* the frame bytes [fr + 32, fr + 36) are addressable: their shadow byte reads 4 *)
      match goal with
      | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (ADD : addressable mm (fr + 32) 4);
          [ split; [lia|]; split; [lia|]; split; [unfold APPMEM_END; lia|];
            intros i Hi; split;
            [ replace (fr + 32 + i) with (fr + (32 + i)) by lia; apply FAP; lia
            | eexists; split;
              [ replace (shadow_addr (fr + 32 + i)) with (fr / 8 + off + 4)
                  by (unfold shadow_addr; rewrite Hoff; clear -FR8 Hi; Z.div_mod_to_equations; lia);
                apply c34_rd1; eassumption
              | unfold shadow_ok; right;
                match goal with | |- _ /\ ?k <= 7 => replace k with 4 by (vm_compute; reflexivity) end;
                split; [clear -FR8 Hi; Z.div_mod_to_equations; lia | lia] ] ] | ]
      end.
      (* 0x86f64: build_dt1_single (o, 0, the four digits at fr + 32, 4) *)
      step.
      destruct BOX as [BOX]. destruct BOX as (GDSP & GOFS & GPFS & HOw & HPw & AOrt & GPFR & LP).
      pose proof HBD as HB0. unfold build_dt1_single_contract_F_on, BUILD_DT1_SINGLE, BUILD_DT1_SINGLE_K in HB0.
      eapply evtF_cut.
      { eapply HB0 with (ob := zeros 32) (D := digits (rw16 row 266)).
        - rewrite (unsigned_lit spc) by lia.
          destruct (stk_split rsegs _ (bv_unsigned sp - 4272) (spc - 2272) (bv_unsigned sp)
                      (stk_mono m _ _ _ ST0 WM RM) ltac:(lia)) as (_ & STd).
          destruct (stk_split rsegs _ (spc - 2272) spc (bv_unsigned sp) STd ltac:(lia)) as (STe & _).
          exact STe.
        - rewrite (unsigned_lit 4) by lia. lia.
        - rewrite (unsigned_lit o) by lia. exact Ho0.
        - rewrite (unsigned_lit o) by lia. lia.
        - rewrite (unsigned_lit o) by lia. eassumption.
        - rewrite (unsigned_lit (fr + 32)), (unsigned_lit 4) by lia. lia.
        - rewrite (unsigned_lit 4) by lia. unfold digits. cbn [map length]. reflexivity.
        - rewrite (unsigned_lit (fr + 32)) by lia. exact HD.
        - rewrite (unsigned_lit o), (unsigned_lit (fr + 32)), (unsigned_lit 4) by lia. lia.
        - rewrite (unsigned_lit o), (unsigned_lit spc) by lia. lia.
        - rewrite (unsigned_lit (fr + 32)), (unsigned_lit 4), (unsigned_lit spc) by lia. lia.
        - exact MI.
        - apply (BRAC (Wf sp FS fr j n ++ [(o, o + 32)])); [unfold Wf, shadow_addr; cbn [app]; exact MU | exact SUB].
        - (* route (C), HD site 5: build_dt1_single's region is the word cover of its source, the digits
             [fr + 32, fr + 36) in the frame (SRfr), and of its destination [o + 20, o + 24) in o (R's 5th
             disjunct); SR0 is carried from m to the call's memory *)
          apply (mbHD_bd (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) _ o (fr + 32) 4
                   (shadow_rw_on_mono_mem _ m _ SR0 WM RM)); [lia | lia | lia | |].
          + intros a Ha. exact (SRfr (fr + 32) 4 a ltac:(lia) ltac:(lia) ltac:(lia) Ha).
          + intros a Ha.
            exact (mbHB_R_o (bv_unsigned sp) FS p b o row nb (o + 20) 4 a ltac:(lia) Ho0 ltac:(lia) ltac:(lia) Ha).
        - rewrite (unsigned_lit spc) by lia. unfold HIGHMEM_BEG. lia.
        - rewrite (unsigned_lit spc) by lia. unfold APPMEM_END. lia.
        - rewrite (unsigned_lit o) by lia.
          apply (CADDR _ o 32 Hp0 Ho0 HK);
            [unfold Wf, shadow_addr; cbn [app]; exact MU | exact AOm | lia].
        - rewrite (unsigned_lit (fr + 32)), (unsigned_lit 4) by lia. exact ADD.
        - rewrite (unsigned_lit o) by lia. exact AOe.
        - rewrite (unsigned_lit (fr + 32)), (unsigned_lit 4) by lia.
          right. replace (fr + 32 + 4) with (fr + 36) by lia. apply FAP. lia.
        - rewrite (unsigned_lit (fr + 32)), (unsigned_lit 4) by lia.
          right. replace (fr + 32 + 7) with (fr + 39) by lia. apply FAP. lia.
        - rewrite (unsigned_lit o) by lia. exact AOrt.
        (* the footprint (build_dt1_single_contract_F of a Theorem Labs lane 6faf362962e: rng_bytes, the image range, the
           callee's window and its 8-aligned shadow cover, the runtime words, o and its shadow, the digits and
           their shadow) *)
        - exact RBY.
        - eapply rng_sub; [exact RIMG | unfold IMG_LO, IMG_HI; lia | unfold IMG_LO, IMG_HI; lia].
        - rewrite (unsigned_lit spc) by lia. eapply rng_sub; [exact RWIN | lia | lia].
        - rewrite (unsigned_lit spc) by lia.
          apply (mbF_shw RNG (bv_unsigned sp - 4272) 4272 (spc - 2272) 2272 KWIN); lia.
        - eapply rng_sub; [exact RIMG | unfold RT_LO; lia | unfold RT_LO, RT_HI; lia].
        - rewrite (unsigned_lit o) by lia. exact ROUTr.
        - rewrite (unsigned_lit o) by lia. apply (ROUTk o (o + 31)); lia.
        - rewrite (unsigned_lit (fr + 32)), (unsigned_lit 4) by lia. eapply rng_sub; [exact RFRM | lia | lia].
        - right. rewrite (unsigned_lit (fr + 32)), (unsigned_lit 4) by lia.
          apply (KFRM (fr + 32) (fr + 32 + 4 - 1)); lia. }
      intros ms' PO.
      destruct PO as (u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & mc2 & E
                      & HB2 & _ & _ & MU2 & WM2 & MI2 & ST2 & AC2 & SR2).
      subst ms'.
      rewrite (unsigned_lit o) in HB2, MU2 by lia.
      rewrite (unsigned_lit spc) in MU2, ST2 by lia.
      rewrite (unsigned_lit 4) in HB2, MU2 by lia.
      rewrite (unsigned_lit 0) in HB2 by lia.
      change (Z.to_nat 4) with 4%nat in HB2.
      assert (LD32 : length (dt1_out 4 0 (digits (rw16 row 266)) (zeros 32)) = 32%nat).
      { unfold dt1_out. rewrite length_app.
        rewrite (dt1_body_length 4 0 (digits (rw16 row 266)) (zeros 32)
                   ltac:(unfold digits; cbn [map length]; reflexivity)
                   ltac:(unfold zeros; rewrite repeat_length; reflexivity)
                   ltac:(lia)).
        cbn [length]. lia. }
      match type of MU2 with
      | munch ?Wc ?mpre _ =>
          assert (RM2 : rd_mono mpre mc2);
          [ apply (rd_mono_list _ _ _ MU2);
            apply Forall_cons;
              [cbn [fst snd]; intros y Hy; apply (rd_of_stk _ _ _ ST2); clear -Hy; lia|];
            apply Forall_cons;
              [cbn [fst snd]; intros y Hy; apply (rd_of_bytes _ _ _ HB2); clear -Hy LD32; lia|];
            apply Forall_cons;
              [cbn [fst snd]; intros y Hy; apply (rd_of_bytes _ _ _ HB2); clear -Hy LD32; lia|];
            apply Forall_nil | ];
          match type of MU with
          | munch ?W _ _ =>
              assert (MU3 : munch W m mc2);
              [ apply (munch_trans W m mpre mc2); [exact MU|];
                eapply munch_weaken; [|exact MU2];
                unfold sub_fp; cbn [outside]; intros xx Hxx;
                repeat split; try exact I; clear -Hxx Gspb GAlo; lia | ]
          end;
          match type of SV with
          | rw_cells _ _ ?Aa ?cs =>
              assert (SV2 : rw_cells rsegs mc2 Aa cs);
              [ apply (acl_rw Wc mpre mc2 Aa cs SV MU2 WM2);
                intros xx Hxx; cbn [SAVES cells_size csize Nat.add] in Hxx;
                cbn [outside fst snd]; repeat split; try exact I; clear -Hxx HOw Gspb GAlo; lia | ]
          end;
          assert (HH2 : bytes_at rsegs mc2 FS (le8 hh));
          [ apply (fl_bytes Wc mpre mc2 FS (le8 hh) HH MU2);
            intros xx Hxx; rewrite length_le8 in Hxx; cbn [Z.of_nat] in Hxx;
            cbn [outside fst snd]; repeat split; try exact I; clear -Hxx GFSsz Gspb GAlo GOFS; lia | ];
          assert (F56b : bytes_at rsegs mc2 (fr + 56) (le8 w56));
          [ apply (fl_bytes Wc mpre mc2 (fr + 56) (le8 w56) F56 MU2);
            intros xx Hxx; rewrite length_le8 in Hxx; cbn [Z.of_nat] in Hxx;
            cbn [outside fst snd]; repeat split; try exact I; clear -Hxx GDSP GOFR; lia | ]
      end.
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3.
      pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      clear MU WM RM SV HH F56 HD ADD HOC MU2 WM2 RM2.
      pose proof (C34Box _ (conj GDSP (conj GOFS (conj GPFS (conj HOw (conj HPw (conj AOrt (conj GPFR LP)))))))) as BOX2.
      clear GDSP GOFS GPFS HOw HPw AOrt GPFR LP.
      replace (ret_pc (Z_to_bv 64 552808)) with (Z_to_bv 64 552808)
        by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      step. step.
      c34_wst (fr / 8 + off + 4) 1%nat. step. store_done.
      step.
      eapply Hrel.
      + exact HK.
      + replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0).
        replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho0).
        cbn [orb]. rewrite Hb, mb_rc3. unfold fwm.
        replace (rw16 row 266 <=? 9999) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      + replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0).
        replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho0).
        cbn [orb]. unfold BI.
        split; [unfold Wf, shadow_addr; cbn [app]; exact MU3|].
        split; [exact WM3|]. split; [exact RM3|]. split; [exact MI2|].
        split; [exact SV2|]. split; [exists hh; exact HH2 | exact F56b].
      + replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0).
        replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho0).
        cbn [orb]. rewrite Hb, mb_synth3. unfold fwm.
        replace (rw16 row 266 <=? 9999) with true by (symmetry; apply Z.leb_le; lia).
        unfold dt1s.
        replace (length (digits (rw16 row 266))) with 4%nat
          by (unfold digits; cbn [map length]; reflexivity).
        exact HB2.
    - (* w > 9999: no call, the frame shadow is reset and the release follows *)
      nf.
      do 3 step.
      c34_wst (fr / 8 + off + 4) 1%nat. step. store_done.
      step.
      eapply Hrel.
      + exact HK.
      + replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0).
        replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho0).
        cbn [orb]. rewrite Hb, mb_rc3. unfold fwm.
        replace (rw16 row 266 <=? 9999) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0).
        replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho0).
        cbn [orb]. unfold BI.
        split; [unfold Wf, shadow_addr; cbn [app]; exact MU|].
        split; [exact WM|]. split; [exact RM|]. split; [exact MI|].
        split; [exact SV|]. split; [exists hh; exact HH | exact F56].
      + replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0).
        replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho0).
        cbn [orb]. rewrite Hb, mb_synth3. unfold fwm.
        replace (rw16 row 266 <=? 9999) with false by (symmetry; apply Z.leb_gt; lia).
        exact (mb_rw1 _ _ _ _ _ HOC).
  Qed.

  Lemma c34_case4F : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    b = 4 -> p <> 0 -> o <> 0 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 (zeros 32)] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x8691c) fc None mc (seg_rom rsegs)).
  Proof using All.
    mbF_open HRNG.
    intros fr f spc j n w56 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
      Hb Hp0 Ho0 HK HB HOC.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    destruct (c34_geo sp tp m p b o FS off A row nb ob Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HP HO
      fr f spc j n w56 Hp0 Ho0 HK) as
      (GA32 & GAlo & GFS0 & GFSsz & Gn & Gj & GFR8 & GFRlo & GFRhi & Gspb & GDSP &
       GOFR & GPFR & GOFS & GPFS & GOFL & GPFL).
    destruct (fk_facts sp tp m p o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 fr f spc j n w56 HK)
      as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SWv & SH1 & SH2).
    pose proof (c34_sub_post sp m p b o FS A row nb ob HA HS16 Rp Rb Ro HP HO fr f spc j n w56 Ho0 HK) as SUB.
    destruct (HP Hp0) as (Hp8 & Lrow & HRm & HPw & HPo).
    destruct (AO Ho0) as (AOm & AOe & AOrt).
    destruct (HO Ho0) as (_ & HOw & _).
    pose proof (AP Hp0) as APm.
    pose proof (br_ac sp tp m p b o FS row nb ob AC0 HHM HAE FP0 Rp Rb Ro HP HO AO) as BRAC.
    pose proof (c34_addr sp tp m p b o FS off A row nb ob Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HP HO AO
                    fr f spc j n w56) as CADDR.
    destruct HB as (MU & WM & RM & MI & SV & (hh & HH) & F56).
    unfold Wf in MU. cbn [app] in MU. unfold shadow_addr in MU.
    assert (LHM : 17594333495296 <= bv_unsigned sp - 4272) by (clear -HHM; unfold HIGHMEM_BEG in HHM; lia).
    assert (LAE : bv_unsigned sp <= 140737488355328) by (clear -HAE; unfold APPMEM_END in HAE; lia).
    assert (APe : p + 296 <= 140737488355328)
      by (clear -APm; destruct APm as (_ & _ & He & _); unfold APPMEM_END in He; lia).
    assert (AOq : o + 32 <= 140737488355328)
      by (clear -AOm; destruct AOm as (_ & _ & He & _); unfold APPMEM_END in He; lia).
    assert (LP : p + 296 <= 2147450880 \/ 17594333495296 <= p)
      by (clear -APm sp m; apply (app_range sp p 296);
          [lia | intros i Hi; apply (acl_app_in m p 296); [exact APm | lia]]).
    assert (LO : o + 32 <= 2147450880 \/ 17594333495296 <= o)
      by (clear -AOm sp m; apply (app_range sp o 32);
          [lia | intros i Hi; apply (acl_app_in m o 32); [exact AOm | lia]]).
    assert (LFS : FS + 8 <= 2147450880 \/ 17594333495296 <= FS).
    { clear -FP0 GFS0.
      pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & PL & _). pose proof PL as (_ & _ & _ & PL4 & _).
      unfold FS_SIZE in PL4.
      pose proof (PL4 FS ltac:(lia)) as H1. pose proof (PL4 (FS + 7) ltac:(lia)) as H2.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. clear -H1 H2. lia. }
    (* the eight name bytes live in the function's window, which is addressable at m *)
    assert (AWs : addressable m (A + 35) 8)
      by (apply (acl_addr_sub m (bv_unsigned sp - 4272) 4272); [exact AW0 | clear -GAlo; lia
                                                               | clear; lia | clear -GAlo; lia]).
    assert (AP42 : app_mem (A + 42))
      by (replace (A + 42) with (bv_unsigned sp - 4272 + (A + 42 - (bv_unsigned sp - 4272))) by (clear -GAlo; lia);
          apply (acl_app_in m (bv_unsigned sp - 4272) 4272); [exact AW0 | clear -GAlo; lia]).
    assert (AP43 : app_mem (A + 43))
      by (replace (A + 43) with (bv_unsigned sp - 4272 + (A + 43 - (bv_unsigned sp - 4272))) by (clear -GAlo; lia);
          apply (acl_app_in m (bv_unsigned sp - 4272) 4272); [exact AW0 | clear -GAlo; lia]).
    assert (OUTP : forall x, p <= x < p + 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x)
      by (intros x Hx;
          exact (c34_out sp o FS off fr j n p 296 x SH1 SH2 Hoff
                   ltac:(replace x with (p + (x - p)) by (clear -Hx; lia);
                         apply (acl_app_in m p 296); [exact APm | clear -Hx; lia])
                   Hx ltac:(clear -HPw; lia) ltac:(clear -GPFS; lia) ltac:(clear -GPFL; lia)
                   ltac:(clear -GPFR; lia) ltac:(clear -HPo Ho0; lia) ltac:(clear -Gn; lia))).
    assert (HRc : bytes_at rsegs mc p row).
    { apply (fl_bytes (Wf sp FS fr j n ++ [(o, o + 32)]) m mc p row HRm);
        [unfold Wf, shadow_addr; cbn [app]; exact MU|].
      intros x Hx. rewrite Lrow in Hx. apply OUTP. clear -Hx; lia. }
    pose proof (rs_rw16_range row 268) as Rw1.
    pose proof (rs_rw16_range row 270) as Rw2.
    pose proof (rs_rw16_range row 272) as Rw3.
    (* the footprint facts of the walk: the row, the output block and the rvb bytes at A + 35 in the window *)
    destruct (RROW Hp0) as (RROWr & RROWc & RROWs & RROWk).
    destruct (ROUT Hp0 Ho0) as (ROUTr & ROUTc & ROUTs & ROUTk).
    assert (RA : rng RNG (A - 64) 128) by (eapply rng_sub; [exact RWIN | clear -GAlo; lia | clear -GAlo; lia]).
    (* PERF: the walk runs with a small context. *)
    clear - Hb Hp0 Ho0 HK MU WM RM MI SV HH F56 HOC HRc Hp8 FR8 Lrow SH1 SH2 Hoff
      GAlo GFRlo GFRhi GFS0 GFSsz Gspb GDSP GOFR GPFR GOFS GPFS LP LO LFS FRA LHM LAE
      Rp Ro APe AOq AOe AOrt FW FAP SWv ST0 SR0 BRAC CADDR SUB HBD Hrel Rsp APm AOm HOw HPw
      AWs AP42 AP43 Rw1 Rw2 Rw3 ob
      RIMG RWIN KWIN RBY RROWr RROWc ROUTr ROUTk RA.
    pose proof (C34Box _ (conj GDSP (conj GOFS (conj GPFS (conj GOFR (conj LP (conj LO (conj LFS (conj FRA AOrt))))))))) as BOX.
    clear GDSP GOFS GPFS GOFR LP LO LFS FRA AOrt.
    (* 0x8691c: the two zero bytes of the rvb row at A + 35, A + 36 *)
    step. step.
    c34_wst (A + 35) 1%nat. step. c34_keep (A + 35). store_done.
    step. nf.
    step. rewrite (unsigned_lit p) by lia. rewrite rc_land7, Hp8.
    c34_wst (A + 36) 1%nat. step. c34_keep (A + 36). store_done.
    step. nf.
    step. step. step. nf.
    (* 0x86944: the checked load of the first word and its two bytes *)
    step. try (rewrite (unsigned_lit p) by lia).
    c34_facts CADDR Lrow HK 268 268%nat ADa SHa RXa RDa.
    chk_core (p + 268) RXa (Z_to_bv 5 12) SHa pre_sr add1.
    step. try rewrite rs_zx16.
    step. step. step.
    c34_wst (A + 37) 1%nat. step. c34_keep (A + 37). store_done.
    step. nf.
    step.
    c34_wst (A + 38) 1%nat. step. c34_keep (A + 38). store_done.
    step. nf.
    (* 0x8697c: the second word *)
    step. try (rewrite (unsigned_lit p) by lia).
    c34_facts CADDR Lrow HK 270 270%nat ADb SHb RXb RDb.
    chk_core (p + 270) RXb (Z_to_bv 5 12) SHb pre_sr add1.
    step. try rewrite rs_zx16.
    step. step. step.
    c34_wst (A + 39) 1%nat. step. c34_keep (A + 39). store_done.
    step. nf.
    c34_wst (A + 40) 1%nat. step. c34_keep (A + 40). store_done.
    (* 0x869ac: the third word *)
    step. try (rewrite (unsigned_lit p) by lia).
    c34_facts CADDR Lrow HK 272 272%nat ADc SHc RXc RDc.
    chk_core (p + 272) RXc (Z_to_bv 5 12) SHc pre_sr add1.
    step. step. step. nf.
    step. try rewrite rs_zx16.
    step. step.
    c34_wst (A + 41) 1%nat. step. c34_keep (A + 41). store_done.
    step. nf.
    c34_wst (A + 42) 1%nat. step. c34_keep (A + 42). store_done.
    step. step. step. step.
    (* the eight bytes at A + 35 read back as the rvb row *)
    match goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (HD : bytes_at rsegs mm (A + 35) (rvb row));
        [ eapply bytes_at_ext;
          [ apply (c34_app2 _ (A + 35) (A + 36)); [eassumption | | simpl_sizes; lia];
            apply (c34_app2 _ (A + 36) (A + 37)); [eassumption | | simpl_sizes; lia];
            apply (c34_app2 _ (A + 37) (A + 38)); [eassumption | | simpl_sizes; lia];
            apply (c34_app2 _ (A + 38) (A + 39)); [eassumption | | simpl_sizes; lia];
            apply (c34_app2 _ (A + 39) (A + 40)); [eassumption | | simpl_sizes; lia];
            apply (c34_app2 _ (A + 40) (A + 41)); [eassumption | | simpl_sizes; lia];
            apply (c34_app2 _ (A + 41) (A + 42)); [eassumption | eassumption | simpl_sizes; lia]
          | symmetry; unfold rvb, le1; cbn [app Z_to_le_bytes];
            apply mb_cons; [reflexivity|]; apply mb_cons; [reflexivity|];
            apply mb_cons; [apply mb_whi; clear -Rw1; lia|];
            apply mb_cons; [apply mb_wlo; clear -Rw1; lia|];
            apply mb_cons; [apply mb_whi; clear -Rw2; lia|];
            apply mb_cons; [apply mb_wlo; clear -Rw2; lia|];
            apply mb_cons; [apply mb_whi; clear -Rw3; lia|];
            apply mb_cons; [apply mb_wlo; clear -Rw3; lia|]; reflexivity ] | ]
    end.
    (* 0x869f4: build_dt1_single (o, 1536, the rvb row at A + 35, 8) *)
    step.
    destruct BOX as [BOX]. destruct BOX as (GDSP & GOFS & GPFS & GOFR & LP & LO & LFS & FRA & AOrt).
    pose proof HBD as HB0. unfold build_dt1_single_contract_F_on, BUILD_DT1_SINGLE, BUILD_DT1_SINGLE_K in HB0.
    eapply evtF_cut.
    { eapply HB0 with (ob := zeros 32) (D := rvb row).
      - rewrite (unsigned_lit spc) by lia.
        destruct (stk_split rsegs _ (bv_unsigned sp - 4272) (spc - 2272) (bv_unsigned sp)
                    (stk_mono m _ _ _ ST0 WM RM) ltac:(lia)) as (_ & STd).
        destruct (stk_split rsegs _ (spc - 2272) spc (bv_unsigned sp) STd ltac:(lia)) as (STe & _).
        exact STe.
      - rewrite (unsigned_lit 8) by lia. lia.
      - rewrite (unsigned_lit o) by lia. exact Ho0.
      - rewrite (unsigned_lit o) by lia. lia.
      - rewrite (unsigned_lit o) by lia. eassumption.
      - rewrite (unsigned_lit (A + 35)), (unsigned_lit 8) by lia. lia.
      - rewrite (unsigned_lit 8) by lia. unfold rvb. cbn [length]. reflexivity.
      - rewrite (unsigned_lit (A + 35)) by lia. exact HD.
      - rewrite (unsigned_lit o), (unsigned_lit (A + 35)), (unsigned_lit 8) by lia. lia.
      - rewrite (unsigned_lit o), (unsigned_lit spc) by lia. lia.
      - rewrite (unsigned_lit (A + 35)), (unsigned_lit 8), (unsigned_lit spc) by lia. lia.
      - exact MI.
      - apply (BRAC (Wf sp FS fr j n ++ [(o, o + 32)])); [unfold Wf, shadow_addr; cbn [app]; exact MU | exact SUB].
      - (* route (C), HD site 6: build_dt1_single's region is the word cover of its source, the rvb bytes
           [A + 35, A + 43) in the window (R's 1st disjunct), and of its destination [o + 20, o + 28) in o
           (R's 5th disjunct); SR0 is carried from m to the call's memory *)
        apply (mbHD_bd (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) _ o (A + 35) 8
                 (shadow_rw_on_mono_mem _ m _ SR0 WM RM)); [lia | lia | lia | |].
        + intros a Ha.
          exact (mbHB_R_win (bv_unsigned sp) FS p b o row nb (A + 35) 8 a ltac:(lia) ltac:(lia) ltac:(lia) Ha).
        + intros a Ha.
          exact (mbHB_R_o (bv_unsigned sp) FS p b o row nb (o + 20) 8 a ltac:(lia) Ho0 ltac:(lia) ltac:(lia) Ha).
      - rewrite (unsigned_lit spc) by lia. unfold HIGHMEM_BEG. lia.
      - rewrite (unsigned_lit spc) by lia. unfold APPMEM_END. lia.
      - rewrite (unsigned_lit o) by lia.
        apply (CADDR _ o 32 Hp0 Ho0 HK);
          [unfold Wf, shadow_addr; cbn [app]; exact MU | exact AOm | clear -GOFR; lia].
      - rewrite (unsigned_lit (A + 35)), (unsigned_lit 8) by lia.
        apply (CADDR _ (A + 35) 8 Hp0 Ho0 HK);
          [unfold Wf, shadow_addr; cbn [app]; exact MU | exact AWs | clear -GFRhi GAlo; lia].
      - rewrite (unsigned_lit o) by lia. exact AOe.
      - rewrite (unsigned_lit (A + 35)), (unsigned_lit 8) by lia.
        right. replace (A + 35 + 8) with (A + 43) by lia. exact AP43.
      - rewrite (unsigned_lit (A + 35)), (unsigned_lit 8) by lia.
        right. replace (A + 35 + 7) with (A + 42) by lia. exact AP42.
      - rewrite (unsigned_lit o) by lia. exact AOrt.
      (* the footprint (build_dt1_single_contract_F of a Theorem Labs lane 6faf362962e: rng_bytes, the image range, the
         callee's window and its 8-aligned shadow cover, the runtime words, o and its shadow, the rvb bytes and
         their shadow) *)
      - exact RBY.
      - eapply rng_sub; [exact RIMG | unfold IMG_LO, IMG_HI; lia | unfold IMG_LO, IMG_HI; lia].
      - rewrite (unsigned_lit spc) by lia. eapply rng_sub; [exact RWIN | lia | lia].
      - rewrite (unsigned_lit spc) by lia.
        apply (mbF_shw RNG (bv_unsigned sp - 4272) 4272 (spc - 2272) 2272 KWIN); lia.
      - eapply rng_sub; [exact RIMG | unfold RT_LO; lia | unfold RT_LO, RT_HI; lia].
      - rewrite (unsigned_lit o) by lia. exact ROUTr.
      - rewrite (unsigned_lit o) by lia. apply (ROUTk o (o + 31)); lia.
      - rewrite (unsigned_lit (A + 35)), (unsigned_lit 8) by lia. eapply rng_sub; [exact RA | lia | lia].
      - right. rewrite (unsigned_lit (A + 35)), (unsigned_lit 8) by lia.
        apply (KWIN (A + 35) (A + 35 + 8 - 1)); lia. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & mc2 & E
                    & HB2 & _ & _ & MU2 & WM2 & MI2 & ST2 & AC2 & SR2).
    subst ms'.
    rewrite (unsigned_lit o) in HB2, MU2 by lia.
    rewrite (unsigned_lit spc) in MU2, ST2 by lia.
    rewrite (unsigned_lit 8) in HB2, MU2 by lia.
    rewrite (unsigned_lit 1536) in HB2 by lia.
    change (Z.to_nat 8) with 8%nat in HB2.
    assert (LD32 : length (dt1_out 8 1536 (rvb row) (zeros 32)) = 32%nat).
    { unfold dt1_out. rewrite length_app.
      rewrite (dt1_body_length 8 1536 (rvb row) (zeros 32)
                 ltac:(unfold rvb; cbn [length]; reflexivity)
                 ltac:(unfold zeros; rewrite repeat_length; reflexivity)
                 ltac:(lia)).
      cbn [length]. lia. }
    match type of MU2 with
    | munch ?Wc ?mpre _ =>
        assert (RM2 : rd_mono mpre mc2);
        [ apply (rd_mono_list _ _ _ MU2);
          apply Forall_cons;
            [cbn [fst snd]; intros y Hy; apply (rd_of_stk _ _ _ ST2); clear -Hy; lia|];
          apply Forall_cons;
            [cbn [fst snd]; intros y Hy; apply (rd_of_bytes _ _ _ HB2); clear -Hy LD32; lia|];
          apply Forall_cons;
            [cbn [fst snd]; intros y Hy; apply (rd_of_bytes _ _ _ HB2); clear -Hy LD32; lia|];
          apply Forall_nil | ];
        match type of MU with
        | munch ?W _ _ =>
            assert (MU3 : munch W m mc2);
            [ apply (munch_trans W m mpre mc2); [exact MU|];
              eapply munch_weaken; [|exact MU2];
              unfold sub_fp; cbn [outside]; intros xx Hxx;
              repeat split; try exact I; clear -Hxx Gspb GAlo; lia | ]
        end;
        match type of SV with
        | rw_cells _ _ ?Aa ?cs =>
            assert (SV2 : rw_cells rsegs mc2 Aa cs);
            [ apply (acl_rw Wc mpre mc2 Aa cs SV MU2 WM2);
              intros xx Hxx; cbn [SAVES cells_size csize Nat.add] in Hxx;
              cbn [outside fst snd]; repeat split; try exact I; clear -Hxx HOw Gspb GAlo; lia | ]
        end;
        assert (HH2 : bytes_at rsegs mc2 FS (le8 hh));
        [ apply (fl_bytes Wc mpre mc2 FS (le8 hh) HH MU2);
          intros xx Hxx; rewrite length_le8 in Hxx; cbn [Z.of_nat] in Hxx;
          cbn [outside fst snd]; repeat split; try exact I; clear -Hxx GFSsz Gspb GAlo GOFS; lia | ];
        assert (F56b : bytes_at rsegs mc2 (fr + 56) (le8 w56));
        [ apply (fl_bytes Wc mpre mc2 (fr + 56) (le8 w56) F56 MU2);
          intros xx Hxx; rewrite length_le8 in Hxx; cbn [Z.of_nat] in Hxx;
          cbn [outside fst snd]; repeat split; try exact I; clear -Hxx GDSP GOFR; lia | ]
    end.
    pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3.
    pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
    clear MU WM RM SV HH F56 HD HOC HRc.
    replace (ret_pc (Z_to_bv 64 551416)) with (Z_to_bv 64 551416)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    step. step.
    eapply Hrel.
    + exact HK.
    + replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0).
      replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho0).
      cbn [orb]. rewrite Hb, mb_rc4. reflexivity.
    + replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0).
      replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho0).
      cbn [orb]. unfold BI.
      split; [unfold Wf, shadow_addr; cbn [app]; exact MU3|].
      split; [exact WM3|]. split; [exact RM3|]. split; [exact MI2|].
      split; [exact SV2|]. split; [exists hh; exact HH2 | exact F56b].
    + replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0).
      replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho0).
      cbn [orb]. rewrite Hb, mb_synth4. unfold dt1s.
      replace (length (rvb row)) with 8%nat by (unfold rvb; cbn [length]; reflexivity).
      exact HB2.
  Qed.
End Case34F.
