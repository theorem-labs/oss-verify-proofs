(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDepotAlloc2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.Bo_code_8cef4_8dab4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3.BoDepotAlloc.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition sa_hmem (M : word -> option byte) (sp ra s0v S : word) (tot cnt : Z) : word -> option byte :=
  wbytes (wbytes (wbytes M (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v)) S (LE8 (Z_to_bv 64 (tot + cnt))).

Section HEADSAME.
  Variables (M rom : word -> option byte) (sp ra s0v S idxp packp : word) (tot cnt : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H10 : getr regs 10 = S.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 cnt.
  Hypothesis H12 : getr regs 12 = idxp.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hcnt : (1 <= cnt <= 256)%Z.
  Hypothesis Htot : (0 <= tot /\ tot + cnt < 2 ^ 32)%Z.
  Hypothesis Hsame : (tot / 2 ^ 20 = (tot + cnt - 1) / 2 ^ 20)%Z.                 (* [comment removed for export] *)
  Hypothesis HS : (U S mod 8 = 0 /\ U S + 2 ^ 20 <= 2 ^ 32 /\ (U S + 2 ^ 20 <= U sp - 16 \/ U sp <= U S))%Z.
  Hypothesis Rtot : rdn BSEGS M S 8 = Some (LE8 (Z_to_bv 64 tot)).
  Hypothesis SOKS : store_ok BSEGS M S 8 = true.
  Hypothesis Hstk : store_ok BSEGS M (at_ sp (-16)) 16 = true.

  Lemma sa_head_same :
    exists r, msteps BSEGS (mkst regs (0x8d018 : word) M rom) (mkst r (0x8d044 : word) (sa_hmem M sp ra s0v S tot cnt) rom)
      /\ getr r 2 = at_ sp (-16) /\ getr r 5 = Z_to_bv 64 (tot / 2 ^ 20) /\ getr r 8 = Z_to_bv 64 tot
      /\ getr r 11 = S /\ getr r 12 = idxp
      /\ regs_agree (fun i : reg => In i [2; 5; 6; 8; 10; 11; 14; 15]) regs r.
  Proof using Hstk SOKS Rtot HS Hsame Htot Hcnt Hsp H12 H11 H10 H8 H2 H1.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range S) as HSr.
    destruct Hsp as [S1 S2]. destruct HS as (S8 & S32 & SF). destruct Htot as [T0 T1].
    set (MF := wbytes (wbytes M (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v)).
    assert (OUTF : forall x : word, (U x < U sp - 16 \/ U sp <= U x)%Z -> MF x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MF in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GRF : mem_grows M MF) by ((lazymatch goal with |- ?G => let G' := eval unfold MF in G in change_no_check G' end); do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (RtotF : rdn BSEGS MF S 8 = Some (LE8 (Z_to_bv 64 tot))).
    { rewrite <- Rtot. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn in Hx. apply OUTF. lia. }
    assert (EA : v_add (Z_to_bv 64 tot) (Z_to_bv 64 cnt) = Z_to_bv 64 (tot + cnt)) by ((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv tot), (u_Z2bv cnt) by lia; reflexivity).
    wd_eexists. split.
    - an F_8d018 D_8d018.                              (* [comment removed for export] *)
      fsd F_8d01c D_8d01c (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8d020 D_8d020 (at_ sp (-16)).              (* [comment removed for export] *)
      change (wbytes (wbytes M _ _) _ _) with MF.
      an F_8d024 D_8d024.                              (* [comment removed for export] *)
      an F_8d028 D_8d028.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 (Z_to_bv 64 tot)) (v := Z_to_bv 64 tot);
          [exact F_8d02c | reflexivity | exact D_8d02c
          | gres; rwH; exact S8
          | gres; rwH; exact RtotF
          | apply bytes_le_to_Z_8
          | gres; rwH; eapply store_ok_mono; [exact GRF | exact SOKS]]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. rewrite EA. change (wbytes MF S _) with (sa_hmem M sp ra s0v S tot cnt).
      av F_8d030 D_8d030 (Z_to_bv 64 (cnt - 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8d034 D_8d034 (Z_to_bv 64 (tot / 2 ^ 20)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv tot) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8d038 D_8d038 (Z_to_bv 64 (tot + cnt - 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8d03c D_8d03c (Z_to_bv 64 ((tot + cnt - 1) / 2 ^ 20)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv (tot + cnt - 1)) by lia; reflexivity).   (* [comment removed for export] *)
      ab_ft F_8d040 D_8d040 ltac:(rwH; rewrite Hsame; (lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end); rewrite bv_eqb_refl; reflexivity).   (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve.
  Qed.

  Lemma sa_hmem_outside : forall x : word, (U x < U sp - 16 \/ U sp <= U x)%Z -> (U x < U S \/ U S + 8 <= U x)%Z -> sa_hmem M sp ra s0v S tot cnt x = M x.
  Proof using HS Hsp.
    intros x X1 X2. pose proof (u64_range sp) as Hspr. pose proof (u64_range S) as HSr. destruct Hsp as [S1 S2]. (lazymatch goal with |- ?G => let G' := eval unfold sa_hmem in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma sa_hmem_grows : mem_grows M (sa_hmem M sp ra s0v S tot cnt).
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold sa_hmem in G in change_no_check G' end). do 3 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
End HEADSAME.
End FPGen.
End BoDepotAlloc2.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDepotRunC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotLock OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3.BoDepotAlloc BoDepotAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotBlk OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunH OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunS OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition cpre_W (P : word) (q : Z) : Z -> Prop :=
  wun (ivl (U P - 256) 112) (wun (ivl (U P - 136) 8) (wun (ivl 1966216 8) (wun (ivl (1966216 + 16 * q + 28) 4) (ivl (1966216 + 8) 8)))).

Section CPRE.
  Variables (M1 rom : word -> option byte) (P nd b hsh alv lkw : word) (b1 b2 b3 : byte) (hd idz sz tag tot : Z).
  Variable r1 : bvmap 5 word.
  #[local] Abbreviation Q := (at_ P (-112)).
  #[local] Abbreviation spS := (at_ Q (-32)).
  #[local] Abbreviation packp := (at_ Q (-24)).
  #[local] Abbreviation args := (at_ P (-104)).
  #[local] Abbreviation spA := (at_ spS (-64)).
  #[local] Abbreviation spB := (at_ spA (-16)).
  #[local] Abbreviation cnt := (sz + 1)%Z.
  #[local] Abbreviation q := (tot / 2 ^ 20)%Z.
  #[local] Abbreviation BI := (Z_to_bv 64 (U SSW + 16 * q + 16)).
  Hypothesis AT : at_store P nd b hsh hd idz r1 M1.
  Hypothesis HP : (2 ^ 32 + 256 <= U P /\ U P + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsz : (1 <= sz < 255)%Z.
  Hypothesis Htag : (0 <= tag < 256)%Z.
  Hypothesis Htot : (0 <= tot /\ tot + sz + 1 < 2 ^ 32)%Z.
  Hypothesis Hsame : (tot / 2 ^ 20 = (tot + sz) / 2 ^ 20)%Z.
  Hypothesis Rsz : rdn BSEGS M1 (at_ args 8) 4 = Some (LE4 (Z_to_bv 64 sz)).
  Hypothesis Rtag : rdn BSEGS M1 (at_ args 12) 4 = Some (LE4 (Z_to_bv 64 tag)).
  Hypothesis Rtot : rdn BSEGS M1 SSW 8 = Some (LE8 (Z_to_bv 64 tot)).
  Hypothesis Rblk0 : rdn BSEGS M1 BI 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis R_lock : rdn BSEGS M1 (at_ BI 12) 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis V_lock : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U lkw.
  Hypothesis Ralloc : rdn BSEGS M1 (at_ SSW 8) 8 = Some (LE8 alv).
  Hypothesis Hstk : store_ok BSEGS M1 (at_ P (-256)) 112 = true.
  Hypothesis SOKp : store_ok BSEGS M1 packp 8 = true.
  Hypothesis SOKS : store_ok BSEGS M1 SSW 8 = true.
  Hypothesis SOKl : store_ok BSEGS M1 (at_ BI 12) 4 = true.
  Hypothesis SOKa : store_ok BSEGS M1 (at_ SSW 8) 8 = true.

  Lemma store_c_pre_same :
    exists r MP, msteps BSEGS (mkst r1 (0x8cef4 : word) M1 rom) (mkst r (0x82db0 : word) MP rom)
      /\ msum (cpre_W P q) M1 MP
      /\ getr r 1 = (0x8da70 : word) /\ getr r 2 = at_ spB (-32) /\ getr r 10 = Z_to_bv 64 8388608 /\ getr r 11 = Z_to_bv 64 0x21f45
      /\ getr r 8 = at_ BI 12 /\ getr r 9 = BI /\ getr r 19 = args /\ getr r 20 = Z_to_bv 64 sz /\ getr r 21 = Z_to_bv 64 tag
      /\ getr r 23 = Z_to_bv 64 idz
      /\ (forall (k : Z) (v : word), In (k, v) [(-8, (0x8d12c%bv : word)); (-16, Z_to_bv 64 tot); (-24, SSW); (-32, Z_to_bv 64 cnt)]%Z -> rdn BSEGS MP (at_ spB k) 8 = Some (LE8 v))
      /\ rdn BSEGS MP (at_ spA (-8)) 8 = Some (LE8 (0x8cf6c : word)) /\ rdn BSEGS MP (at_ spA (-16)) 8 = Some (LE8 packp)
      /\ (forall (k : Z) (v : word), In (k, v) [(-8, (0x8f234%bv : word)); (-16, nd); (-24, nd); (-32, b); (-40, getr r1 19); (-48, getr r1 20); (-56, Z_to_bv 64 hd)]%Z ->
             rdn BSEGS MP (at_ spS k) 8 = Some (LE8 v))
      /\ rdn BSEGS MP spA 8 = Some (LE8 (Z_to_bv 64 tot))
      /\ rdn BSEGS MP packp 8 = Some (LE8 (Z_to_bv 64 0))
      /\ rdn BSEGS MP SSW 8 = Some (LE8 (Z_to_bv 64 (tot + cnt)))
      /\ regs_agree (fun i : reg => In i put_clob) r1 r.
  Proof using SOKa SOKl SOKS SOKp Hstk Ralloc V_lock R_lock Rblk0 Rtot Rtag Rsz Hsame Htot Htag Hsz HP AT b3 b2 b1 lkw alv hsh.
    pose proof (u64_range P) as HPr. destruct HP as [P1 P2]. destruct Htot as [T0 T32].
    assert (USS : U SSW = 1966216%Z) by reflexivity.
    assert (UQ : U Q = (U P - 112)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspS : U spS = (U P - 144)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Upk : U packp = (U P - 136)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Uargs : U args = (U P - 104)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspA : U spA = (U P - 208)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspB : U spB = (U P - 224)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Q20 : (0 <= q < 2 ^ 12)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (UBI : U BI = (1966216 + 16 * q + 16)%Z) by (rewrite USS; rewrite u_Z2bv by lia; reflexivity).
    assert (UBL : U (at_ BI 12) = (1966216 + 16 * q + 28)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (USA : U (at_ SSW 8) = (1966216 + 8)%Z) by (rewrite at_u by (rewrite USS; lia); rewrite USS; reflexivity).
    destruct AT as (A1 & A2 & A8 & A10 & A11 & A12 & A9 & A18 & A21 & A23 & RhshH & RraH & Rs0H).
    assert (SUB : forall (a : word) (n : nat), (U P - 256 <= U a)%Z -> (U a + Z.of_nat n <= U P - 144)%Z -> store_ok BSEGS M1 a n = true).
    { intros a n X1 X2. eapply (store_ok_sub BSEGS M1 (at_ P (-256)) _ 112); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    (* [comment removed for export] *)
    destruct (st_pre M1 rom spS (0x8f234 : word) SSW args packp nd nd b (getr r1 19) (getr r1 20) (getr r1 21) sz tag r1
                A1 A2 A8 A9 A18 eq_refl eq_refl eq_refl A10 A11 A12
                ltac:(rewrite UspS; lia) ltac:(rewrite UspS, Uargs; lia) ltac:(rewrite UspS, Upk; lia) Hsz Htag Rsz Rtag)
      as (r2 & RUN1 & B1 & B2 & B10 & B11 & B12 & B13 & B8 & B9 & B18 & B19 & B20 & B21 & AG1).
    { apply SUB; [rewrite at_u by (rewrite UspS; lia); rewrite UspS; lia | rewrite at_u by (rewrite UspS; lia); rewrite UspS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { exact SOKp. }
    set (Ma := st_m1 M1 spS (0x8f234 : word) nd nd b (getr r1 19) (getr r1 20) (getr r1 21) packp) in *.
    assert (Pa : forall x : word, (U x < U P - 208 \/ U P - 144 <= U x)%Z -> (U x < U P - 136 \/ U P - 128 <= U x)%Z -> Ma x = M1 x).
    { intros x X1 X2. (lazymatch goal with |- ?G => let G' := eval unfold Ma in G in change_no_check G' end). apply st_m1_outside; rewrite ?UspS, ?Upk; lia. }
    assert (Ga : mem_grows M1 Ma) by apply st_m1_grows.
    (* [comment removed for export] *)
    destruct (sa_head_same Ma rom spA (0x8cf6c : word) packp SSW spA tot cnt r2 B1 B2 B8 B10 B11 B12
                ltac:(rewrite UspA; lia) ltac:(lia) ltac:(lia) ltac:(replace (tot + cnt - 1)%Z with (tot + sz)%Z by lia; exact Hsame)
                ltac:(rewrite USS, UspA; split; [reflexivity | lia]))
      as (r3 & RUN2 & C2 & C5 & C8 & C11 & C12 & AG2).
    { rewrite <- Rtot. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn in Hx. apply Pa; lia. }
    { eapply store_ok_mono; [exact Ga | exact SOKS]. }
    { eapply store_ok_mono; [exact Ga|]. apply SUB; [rewrite at_u by (rewrite UspA; lia); rewrite UspA; lia | rewrite at_u by (rewrite UspA; lia); rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    set (Mb := sa_hmem Ma spA (0x8cf6c : word) packp SSW tot cnt) in *.
    assert (Pb : forall x : word, (U x < U P - 224 \/ U P - 208 <= U x)%Z -> (U x < 1966216 \/ 1966216 + 8 <= U x)%Z -> Mb x = Ma x).
    { intros x X1 X2. (lazymatch goal with |- ?G => let G' := eval unfold Mb in G in change_no_check G' end). apply sa_hmem_outside; rewrite ?UspA, ?USS; first [lia | split; [reflexivity | lia]]. }
    assert (Gb : mem_grows M1 Mb) by (eapply mem_grows_trans; [exact Ga | apply sa_hmem_grows]).
    (* [comment removed for export] *)
    destruct (sa_tail_cpre Mb rom spA SSW spA (Z_to_bv 64 0) tot r3 C2 C5 C8 C11 C12
                ltac:(rewrite UspA; lia) ltac:(lia) ltac:(rewrite USS, UspA; lia) ltac:(rewrite USS, UspA; lia))
      as (r4 & RUN3 & D1 & D10 & D2 & D8 & AG3).
    { eapply store_ok_mono; [exact Gb|]. apply SUB; [rewrite UspA; lia | rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { rewrite <- Rblk0. apply rdn_ext; [rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite UBI in Hx. cbn in Hx. rewrite Pb by lia. apply Pa; lia. }
    { reflexivity. }
    set (Mc := sa_tmem Mb spA tot) in *.
    assert (Pc : forall x : word, (U x < U P - 208 \/ U P - 200 <= U x)%Z -> Mc x = Mb x).
    { intros x X1. (lazymatch goal with |- ?G => let G' := eval unfold Mc, sa_tmem in G in change_no_check G' end). rewrite wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?UspA; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (Gc : mem_grows M1 Mc) by (eapply mem_grows_trans; [exact Gb | (lazymatch goal with |- ?G => let G' := eval unfold Mc, sa_tmem in G in change_no_check G' end); apply wbytes_grows]).
    assert (THRUc : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z -> (U a + Z.of_nat n <= U P - 224 \/ U P - 128 <= U a)%Z ->
              (U a + Z.of_nat n <= 1966216 \/ 1966216 + 8 <= U a)%Z -> rdn BSEGS M1 a n = Some v -> rdn BSEGS Mc a n = Some v).
    { intros a n v X0 X1 X2 Hr. rewrite <- Hr. apply rdn_ext; [exact X0|]. intros x Hx. rewrite Pc by lia. rewrite Pb by lia. apply Pa; lia. }
    (* [comment removed for export] *)
    destruct (bi_pre Mc rom spB (0x8d12c : word) (Z_to_bv 64 tot) (getr r4 9) (getr r4 18) BI SSW alv lkw b1 b2 b3 r4 D1 D2 D8 eq_refl eq_refl D10)
      as (r5 & RUN4 & E1 & E2 & E10 & E11 & E8 & E9 & AG4).
    { rewrite (AG3 11%bv) by nin. exact C11. }
    { rewrite UspB. lia. }
    { rewrite UBI, USS. split; [reflexivity | lia]. }
    { rewrite UBI. split; [| lia]. replace (1966216 + 16 * q + 16)%Z with ((245779 + 2 * q) * 8)%Z by lia. apply Z_mod_mult. }
    { apply THRUc; [rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact R_lock]. }
    { exact V_lock. }
    { apply THRUc; [rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rblk0]. }
    { apply THRUc; [rewrite USA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Ralloc]. }
    { eapply store_ok_mono; [exact Gc | exact SOKl]. }
    { eapply store_ok_mono; [exact Gc | exact SOKa]. }
    { eapply store_ok_mono; [exact Gc|]. apply SUB; [rewrite at_u by (rewrite UspB; lia); rewrite UspB; lia | rewrite at_u by (rewrite UspB; lia); rewrite UspB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    set (Md := bi_m1 Mc spB (0x8d12c : word) (Z_to_bv 64 tot) (getr r4 9) (getr r4 18) BI SSW alv b1 b2 b3) in *.
    assert (Pd : forall x : word, (U x < U P - 256 \/ U P - 224 <= U x)%Z -> (U x < 1966216 + 16 * q + 28 \/ 1966216 + 16 * q + 32 <= U x)%Z ->
              (U x < 1966216 + 8 \/ 1966216 + 16 <= U x)%Z -> Md x = Mc x).
    { intros x X1 X2 X3. (lazymatch goal with |- ?G => let G' := eval unfold Md, bi_m1, bi_frame in G in change_no_check G' end).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?UBL, ?USA, ?at_u by (rewrite UspB; lia); rewrite ?UspB; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (Gd : mem_grows M1 Md).
    { eapply mem_grows_trans; [exact Gc|]. (lazymatch goal with |- ?G => let G' := eval unfold Md, bi_m1, bi_frame in G in change_no_check G' end). do 6 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
    assert (S9 : getr r4 9 = SSW) by (rewrite (AG3 9%bv) by nin; rewrite (AG2 9%bv) by nin; exact B9).
    assert (S18 : getr r4 18 = Z_to_bv 64 cnt) by (rewrite (AG3 18%bv) by nin; rewrite (AG2 18%bv) by nin; exact B18).
    exists r5, Md. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; eapply msteps_trans; [exact RUN3 | exact RUN4]|].
    split.
    { apply msum_outside; [| exact Gd]. intros x Hx. unfold cpre_W, wun, ivl in Hx. rewrite Pd by lia. rewrite Pc by lia. rewrite Pb by lia. apply Pa; lia. }
    split; [exact E1|]. split; [exact E2|]. split; [exact E10|]. split; [exact E11|]. split; [exact E8|]. split; [exact E9|].
    split; [rewrite (AG4 19%bv) by nin; rewrite (AG3 19%bv) by nin; rewrite (AG2 19%bv) by nin; exact B19|].
    split; [rewrite (AG4 20%bv) by nin; rewrite (AG3 20%bv) by nin; rewrite (AG2 20%bv) by nin; exact B20|].
    split; [rewrite (AG4 21%bv) by nin; rewrite (AG3 21%bv) by nin; rewrite (AG2 21%bv) by nin; exact B21|].
    split; [rewrite (AG4 23%bv) by nin; rewrite (AG3 23%bv) by nin; rewrite (AG2 23%bv) by nin; rewrite (AG1 23%bv) by nin; exact A23|].
    split.
    { intros k v Hin. rewrite <- S9, <- S18 in Hin. (lazymatch goal with |- ?G => let G' := eval unfold Md, bi_m1 in G in change_no_check G' end).
      assert (K : (-32 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite !rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?UBL, ?USA, ?at_u by (rewrite UspB; lia); rewrite ?UspB; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia.
      (lazymatch goal with |- ?G => let G' := eval unfold bi_frame in G in change_no_check G' end). cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin. }
    assert (THRUd : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z -> (U P - 224 <= U a)%Z -> rdn BSEGS Mc a n = Some v -> rdn BSEGS Md a n = Some v).
    { intros a n v X0 X1 Hr. rewrite <- Hr. apply rdn_ext; [exact X0|]. intros x Hx. apply Pd; lia. }
    assert (THRUcd : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z -> (U P - 200 <= U a)%Z -> rdn BSEGS Mb a n = Some v -> rdn BSEGS Md a n = Some v).
    { intros a n v X0 X1 Hr. apply THRUd; [exact X0 | lia|]. rewrite <- Hr. apply rdn_ext; [exact X0|]. intros x Hx. apply Pc; lia. }
    split.
    { apply THRUd; [rewrite at_u by (rewrite UspA; lia); rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UspA; lia); rewrite UspA; lia|].
      (lazymatch goal with |- ?G => let G' := eval unfold Mc, sa_tmem in G in change_no_check G' end). rewrite rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by (rewrite UspA; lia); rewrite ?UspA; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia.
      (lazymatch goal with |- ?G => let G' := eval unfold Mb, sa_hmem in G in change_no_check G' end). rd8_chain. }
    split.
    { apply THRUd; [rewrite at_u by (rewrite UspA; lia); rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UspA; lia); rewrite UspA; lia|].
      (lazymatch goal with |- ?G => let G' := eval unfold Mc, sa_tmem in G in change_no_check G' end). rewrite rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by (rewrite UspA; lia); rewrite ?UspA; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia.
      (lazymatch goal with |- ?G => let G' := eval unfold Mb, sa_hmem in G in change_no_check G' end). rd8_chain. }
    split.
    { intros k v Hin.
      assert (K : (-56 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply THRUcd; [rewrite at_u by (rewrite UspS; lia); rewrite UspS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UspS; lia); rewrite UspS; lia|].
      transitivity (rdn BSEGS Ma (at_ spS k) 8).
      { apply rdn_ext; [rewrite at_u by (rewrite UspS; lia); rewrite UspS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by (rewrite UspS; lia). rewrite UspS in Hx. cbn in Hx. apply Pb; lia. }
      transitivity (rdn BSEGS (st_frame M1 spS (0x8f234 : word) nd nd b (getr r1 19) (getr r1 20) (getr r1 21)) (at_ spS k) 8).
      { apply rdn_ext; [rewrite at_u by (rewrite UspS; lia); rewrite UspS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by (rewrite UspS; lia). rewrite UspS in Hx. cbn in Hx.
        (lazymatch goal with |- ?G => let G' := eval unfold Ma, st_m1 in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?Upk, ?at_u by (rewrite UspS; lia); rewrite ?UspS; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
      rewrite <- A21 in Hin. (lazymatch goal with |- ?G => let G' := eval unfold st_frame in G in change_no_check G' end). cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin. }
    split.
    { apply THRUd; [rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UspA; lia|]. (lazymatch goal with |- ?G => let G' := eval unfold Mc, sa_tmem in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite UspA. lia. }
    split.
    { apply THRUcd; [rewrite Upk; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Upk; lia|].
      transitivity (rdn BSEGS Ma packp 8).
      { apply rdn_ext; [rewrite Upk; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite Upk in Hx. cbn in Hx. apply Pb; lia. }
      (lazymatch goal with |- ?G => let G' := eval unfold Ma, st_m1 in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite Upk. lia. }
    split.
    { transitivity (rdn BSEGS Mb SSW 8).
      { apply rdn_ext; [rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite USS in Hx. cbn in Hx. rewrite Pd by lia. apply Pc; lia. }
      (lazymatch goal with |- ?G => let G' := eval unfold Mb, sa_hmem in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite USS. lia. }
    apply (regs_agree_trans _ r1 r2); [ra_pc AG1|]. apply (regs_agree_trans _ r2 r3); [ra_pc AG2|]. apply (regs_agree_trans _ r3 r4); [ra_pc AG3 | ra_pc AG4].
  Qed.
End CPRE.
End FPGen.
End BoDepotRunC1.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDepotRunC2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotLock OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3.BoDepotAlloc BoDepotAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotBlk OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunH OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunS OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI BoDepotRunC1.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition cpre_Wx (P : word) (q q1 : Z) : Z -> Prop :=
  wun (cpre_W P q1) (wun (ivl (1966216 + 16 * q + 24) 4) (ivl (1966216 + 16 * q1 + 24) 4)).

Section CPREX.
  Variables (M1 rom : word -> option byte) (P nd b hsh alv lkw : word) (b1 b2 b3 : byte) (hd idz sz tag tot so0 so1 : Z).
  Variable r1 : bvmap 5 word.
  #[local] Abbreviation Q := (at_ P (-112)).
  #[local] Abbreviation spS := (at_ Q (-32)).
  #[local] Abbreviation packp := (at_ Q (-24)).
  #[local] Abbreviation args := (at_ P (-104)).
  #[local] Abbreviation spA := (at_ spS (-64)).
  #[local] Abbreviation spB := (at_ spA (-16)).
  #[local] Abbreviation cnt := (sz + 1)%Z.
  #[local] Abbreviation q := (tot / 2 ^ 20)%Z.
  #[local] Abbreviation q1 := ((tot + (sz + 1)) / 2 ^ 20)%Z.
  #[local] Abbreviation inf := (sa_inf tot).
  #[local] Abbreviation BI := (Z_to_bv 64 (U SSW + 16 * q1 + 16)).
  Hypothesis AT : at_store P nd b hsh hd idz r1 M1.
  Hypothesis HP : (2 ^ 32 + 256 <= U P /\ U P + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsz : (1 <= sz < 255)%Z.
  Hypothesis Htag : (0 <= tag < 256)%Z.
  Hypothesis Htot : (0 <= tot /\ tot + (sz + 1) + (sz + 1) <= 2 ^ 32)%Z.
  Hypothesis Hq1 : ((tot + sz) / 2 ^ 20 = tot / 2 ^ 20 + 1)%Z.                     (* [comment removed for export] *)
  Hypothesis Hso : (0 <= so0 < 2 ^ 32 /\ 0 <= so1 < 2 ^ 32)%Z.
  Hypothesis Rsz : rdn BSEGS M1 (at_ args 8) 4 = Some (LE4 (Z_to_bv 64 sz)).
  Hypothesis Rtag : rdn BSEGS M1 (at_ args 12) 4 = Some (LE4 (Z_to_bv 64 tag)).
  Hypothesis Rtot : rdn BSEGS M1 SSW 8 = Some (LE8 (Z_to_bv 64 tot)).
  Hypothesis Rso0 : rdn BSEGS M1 (st_cell SSW tot) 4 = Some (LE4 (Z_to_bv 64 so0)).
  Hypothesis Rso1 : rdn BSEGS M1 (st_cell SSW (tot + (sz + 1))) 4 = Some (LE4 (Z_to_bv 64 so1)).
  Hypothesis Rblk0 : rdn BSEGS M1 BI 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis R_lock : rdn BSEGS M1 (at_ BI 12) 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis V_lock : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U lkw.
  Hypothesis Ralloc : rdn BSEGS M1 (at_ SSW 8) 8 = Some (LE8 alv).
  Hypothesis Hstk : store_ok BSEGS M1 (at_ P (-256)) 112 = true.
  Hypothesis SOKp : store_ok BSEGS M1 packp 8 = true.
  Hypothesis SOKS : store_ok BSEGS M1 SSW 8 = true.
  Hypothesis SOK0 : store_ok BSEGS M1 (st_cell SSW tot) 4 = true.
  Hypothesis SOK1 : store_ok BSEGS M1 (st_cell SSW (tot + (sz + 1))) 4 = true.
  Hypothesis SOKl : store_ok BSEGS M1 (at_ BI 12) 4 = true.
  Hypothesis SOKa : store_ok BSEGS M1 (at_ SSW 8) 8 = true.

  Lemma store_c_pre_strad :
    exists r MP, msteps BSEGS (mkst r1 (0x8cef4 : word) M1 rom) (mkst r (0x82db0 : word) MP rom)
      /\ msum (cpre_Wx P q q1) M1 MP
      /\ getr r 1 = (0x8da70 : word) /\ getr r 2 = at_ spB (-32) /\ getr r 10 = Z_to_bv 64 8388608 /\ getr r 11 = Z_to_bv 64 0x21f45
      /\ getr r 8 = at_ BI 12 /\ getr r 9 = BI /\ getr r 19 = args /\ getr r 20 = Z_to_bv 64 sz /\ getr r 21 = Z_to_bv 64 tag
      /\ getr r 23 = Z_to_bv 64 idz
      /\ (forall (k : Z) (v : word), In (k, v) [(-8, (0x8d12c%bv : word)); (-16, Z_to_bv 64 (tot + cnt)); (-24, SSW); (-32, Z_to_bv 64 cnt)]%Z -> rdn BSEGS MP (at_ spB k) 8 = Some (LE8 v))
      /\ rdn BSEGS MP (at_ spA (-8)) 8 = Some (LE8 (0x8cf6c : word)) /\ rdn BSEGS MP (at_ spA (-16)) 8 = Some (LE8 packp)
      /\ (forall (k : Z) (v : word), In (k, v) [(-8, (0x8f234%bv : word)); (-16, nd); (-24, nd); (-32, b); (-40, getr r1 19); (-48, getr r1 20); (-56, Z_to_bv 64 hd)]%Z ->
             rdn BSEGS MP (at_ spS k) 8 = Some (LE8 v))
      /\ rdn BSEGS MP spA 8 = Some (LE8 (Z_to_bv 64 (tot + cnt)))
      /\ rdn BSEGS MP packp 8 = Some (LE8 (Z_to_bv 64 (0 + st_full so0 inf + st_full so1 (cnt - inf))))
      /\ rdn BSEGS MP SSW 8 = Some (LE8 (Z_to_bv 64 (tot + cnt + cnt)))
      /\ rdn BSEGS MP (st_cell SSW tot) 4 = Some (LE4 (v_add (Z_to_bv 64 so0) (Z_to_bv 64 inf)))
      /\ rdn BSEGS MP (st_cell SSW (tot + cnt)) 4 = Some (LE4 (v_add (Z_to_bv 64 so1) (Z_to_bv 64 (cnt - inf))))
      /\ q1 = (q + 1)%Z /\ (1 <= inf <= cnt - 1)%Z
      /\ regs_agree (fun i : reg => In i put_clob) r1 r.
  Proof using SOKa SOKl SOK1 SOK0 SOKS SOKp Hstk Ralloc V_lock R_lock Rblk0 Rso1 Rso0 Rtot Rtag Rsz Hso Hq1 Htot Htag Hsz HP AT b3 b2 b1 lkw alv hsh.
    pose proof (u64_range P) as HPr. destruct HP as [P1 P2]. destruct Htot as [T0 T32].
    assert (USS : U SSW = 1966216%Z) by reflexivity.
    assert (UQ : U Q = (U P - 112)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspS : U spS = (U P - 144)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Upk : U packp = (U P - 136)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Uargs : U args = (U P - 104)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspA : U spA = (U P - 208)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspB : U spB = (U P - 224)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    destruct Hso as [SO0 SO1].
    assert (ARI : (0 <= tot mod 2 ^ 20 < 2 ^ 20 /\ 1 <= inf <= cnt - 1 /\ q1 = q + 1 /\ (tot + cnt + cnt - 1) / 2 ^ 20 = q + 1 /\ 0 <= q /\ q + 1 < 2 ^ 12)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold sa_inf in G in change_no_check G' end).
      pose proof (Z.div_mod tot (2 ^ 20) ltac:(lia)) as E1. pose proof (Z.mod_pos_bound tot (2 ^ 20) ltac:(lia)) as B1'.
      pose proof (Z.div_mod (tot + sz) (2 ^ 20) ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (tot + sz) (2 ^ 20) ltac:(lia)) as B2'.
      rewrite Hq1 in E2.
      assert (Q0 : (0 <= tot / 2 ^ 20)%Z) by (apply Z.div_pos; lia).
      split; [exact B1'|]. split; [lia|].
      split. { symmetry. apply (Z.div_unique (tot + cnt) (2 ^ 20) (tot / 2 ^ 20 + 1) (tot + cnt - 2 ^ 20 * (tot / 2 ^ 20 + 1))); lia. }
      split. { symmetry. apply (Z.div_unique (tot + cnt + cnt - 1) (2 ^ 20) (tot / 2 ^ 20 + 1) (tot + cnt + cnt - 1 - 2 ^ 20 * (tot / 2 ^ 20 + 1))); lia. }
      split; [exact Q0|].
      assert (tot / 2 ^ 20 < 2 ^ 12 - 1)%Z; [| lia]. apply Z.div_lt_upper_bound; lia. }
    destruct ARI as (M20 & INF & EQ1 & Q3 & Q0 & Q12).
    assert (Q20 : (0 <= q1 < 2 ^ 12)%Z) by (rewrite EQ1; lia).
    assert (Uc0 : U (st_cell SSW tot) = (1966216 + 16 * q + 24)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite USS; rewrite u_Z2bv by lia; reflexivity).
    assert (Uc1 : U (st_cell SSW (tot + cnt)) = (1966216 + 16 * q1 + 24)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite USS; rewrite u_Z2bv by lia; reflexivity).
    assert (UBI : U BI = (1966216 + 16 * q1 + 16)%Z) by (rewrite USS; rewrite u_Z2bv by lia; reflexivity).
    assert (UBL : U (at_ BI 12) = (1966216 + 16 * q1 + 28)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (USA : U (at_ SSW 8) = (1966216 + 8)%Z) by (rewrite at_u by (rewrite USS; lia); rewrite USS; reflexivity).
    destruct AT as (A1 & A2 & A8 & A10 & A11 & A12 & A9 & A18 & A21 & A23 & RhshH & RraH & Rs0H).
    assert (SUB : forall (a : word) (n : nat), (U P - 256 <= U a)%Z -> (U a + Z.of_nat n <= U P - 144)%Z -> store_ok BSEGS M1 a n = true).
    { intros a n X1 X2. eapply (store_ok_sub BSEGS M1 (at_ P (-256)) _ 112); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    (* [comment removed for export] *)
    destruct (st_pre M1 rom spS (0x8f234 : word) SSW args packp nd nd b (getr r1 19) (getr r1 20) (getr r1 21) sz tag r1
                A1 A2 A8 A9 A18 eq_refl eq_refl eq_refl A10 A11 A12
                ltac:(rewrite UspS; lia) ltac:(rewrite UspS, Uargs; lia) ltac:(rewrite UspS, Upk; lia) Hsz Htag Rsz Rtag)
      as (r2 & RUN1 & B1 & B2 & B10 & B11 & B12 & B13 & B8 & B9 & B18 & B19 & B20 & B21 & AG1).
    { apply SUB; [rewrite at_u by (rewrite UspS; lia); rewrite UspS; lia | rewrite at_u by (rewrite UspS; lia); rewrite UspS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { exact SOKp. }
    set (Ma := st_m1 M1 spS (0x8f234 : word) nd nd b (getr r1 19) (getr r1 20) (getr r1 21) packp) in *.
    assert (Pa : forall x : word, (U x < U P - 208 \/ U P - 144 <= U x)%Z -> (U x < U P - 136 \/ U P - 128 <= U x)%Z -> Ma x = M1 x).
    { intros x X1 X2. (lazymatch goal with |- ?G => let G' := eval unfold Ma in G in change_no_check G' end). apply st_m1_outside; rewrite ?UspS, ?Upk; lia. }
    assert (Ga : mem_grows M1 Ma) by apply st_m1_grows.
    (* [comment removed for export] *)
    assert (Rpka : rdn BSEGS Ma packp 8 = Some (LE8 (Z_to_bv 64 0))) by ((lazymatch goal with |- ?G => let G' := eval unfold Ma, st_m1 in G in change_no_check G' end); apply rdn_wbytes_hit8; rewrite Upk; lia).
    destruct (sa_head_strad Ma rom spA (0x8cf6c : word) packp SSW spA packp tot cnt so0 so1 0 r2 B1 B2 B8 B10 B11 B12 B13
                ltac:(rewrite UspA; lia) ltac:(lia) ltac:(lia) ltac:(replace (tot + cnt - 1)%Z with (tot + sz)%Z by lia; exact Hq1)
                ltac:(lia) ltac:(rewrite USS; split; [reflexivity | lia]) ltac:(rewrite UspA, Upk; lia))
      as (r3 & RUN2 & C2 & C5 & C8 & C11 & C12 & AG2).
    { rewrite <- Rtot. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn in Hx. apply Pa; lia. }
    { rewrite <- Rso0. apply rdn_ext; [rewrite Uc0; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite Uc0 in Hx. cbn in Hx. apply Pa; lia. }
    { rewrite <- Rso1. apply rdn_ext; [rewrite Uc1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite Uc1 in Hx. cbn in Hx. apply Pa; lia. }
    { exact Rpka. }
    { eapply store_ok_mono; [exact Ga | exact SOKS]. }
    { eapply store_ok_mono; [exact Ga | exact SOK0]. }
    { eapply store_ok_mono; [exact Ga | exact SOK1]. }
    { eapply store_ok_mono; [exact Ga | exact SOKp]. }
    { eapply store_ok_mono; [exact Ga|]. apply SUB; [rewrite at_u by (rewrite UspA; lia); rewrite UspA; lia | rewrite at_u by (rewrite UspA; lia); rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    set (Mb := sa_smem Ma spA (0x8cf6c : word) packp SSW packp tot cnt so0 so1 0) in *.
    assert (Pb : forall x : word, (U x < U P - 224 \/ U P - 208 <= U x)%Z -> (U x < 1966216 \/ 1966216 + 8 <= U x)%Z ->
              (U x < 1966216 + 16 * q + 24 \/ 1966216 + 16 * q + 28 <= U x)%Z -> (U x < 1966216 + 16 * q1 + 24 \/ 1966216 + 16 * q1 + 28 <= U x)%Z ->
              (U x < U P - 136 \/ U P - 128 <= U x)%Z -> Mb x = Ma x).
    { intros x X1 X2 X3 X4 X5. (lazymatch goal with |- ?G => let G' := eval unfold Mb, sa_smem in G in change_no_check G' end).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?Uc0, ?Uc1, ?Upk, ?USS, ?at_u by (rewrite UspA; lia); rewrite ?UspA; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (Gb : mem_grows M1 Mb).
    { eapply mem_grows_trans; [exact Ga|]. (lazymatch goal with |- ?G => let G' := eval unfold Mb, sa_smem in G in change_no_check G' end). do 8 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
    (* [comment removed for export] *)
    destruct (sa_tail_cpre Mb rom spA SSW spA (Z_to_bv 64 0) (tot + cnt) r3 C2 C5 C8 C11 C12
                ltac:(rewrite UspA; lia) ltac:(lia) ltac:(rewrite USS, UspA; lia) ltac:(rewrite USS, UspA; lia))
      as (r4 & RUN3 & D1 & D10 & D2 & D8 & AG3).
    { eapply store_ok_mono; [exact Gb|]. apply SUB; [rewrite UspA; lia | rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { rewrite <- Rblk0. apply rdn_ext; [rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite UBI in Hx. cbn in Hx. rewrite Pb by lia. apply Pa; lia. }
    { reflexivity. }
    set (Mc := sa_tmem Mb spA (tot + cnt)) in *.
    assert (Pc : forall x : word, (U x < U P - 208 \/ U P - 200 <= U x)%Z -> Mc x = Mb x).
    { intros x X1. (lazymatch goal with |- ?G => let G' := eval unfold Mc, sa_tmem in G in change_no_check G' end). rewrite wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?UspA; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (Gc : mem_grows M1 Mc) by (eapply mem_grows_trans; [exact Gb | (lazymatch goal with |- ?G => let G' := eval unfold Mc, sa_tmem in G in change_no_check G' end); apply wbytes_grows]).
    assert (THRUc : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z -> (U a + Z.of_nat n <= U P - 224 \/ U P - 128 <= U a)%Z ->
              (U a + Z.of_nat n <= 1966216 \/ 1966216 + 8 <= U a)%Z ->
              (U a + Z.of_nat n <= 1966216 + 16 * q + 24 \/ 1966216 + 16 * q + 28 <= U a)%Z -> (U a + Z.of_nat n <= 1966216 + 16 * q1 + 24 \/ 1966216 + 16 * q1 + 28 <= U a)%Z ->
              rdn BSEGS M1 a n = Some v -> rdn BSEGS Mc a n = Some v).
    { intros a n v X0 X1 X2 X3 X4 Hr. rewrite <- Hr. apply rdn_ext; [exact X0|]. intros x Hx. rewrite Pc by lia. rewrite Pb by lia. apply Pa; lia. }
    (* [comment removed for export] *)
    destruct (bi_pre Mc rom spB (0x8d12c : word) (Z_to_bv 64 (tot + cnt)) (getr r4 9) (getr r4 18) BI SSW alv lkw b1 b2 b3 r4 D1 D2 D8 eq_refl eq_refl D10)
      as (r5 & RUN4 & E1 & E2 & E10 & E11 & E8 & E9 & AG4).
    { rewrite (AG3 11%bv) by nin. exact C11. }
    { rewrite UspB. lia. }
    { rewrite UBI, USS. split; [reflexivity | lia]. }
    { rewrite UBI. split; [| lia]. replace (1966216 + 16 * q1 + 16)%Z with ((245779 + 2 * q1) * 8)%Z by lia. apply Z_mod_mult. }
    { apply THRUc; [rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact R_lock]. }
    { exact V_lock. }
    { apply THRUc; [rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rblk0]. }
    { apply THRUc; [rewrite USA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Ralloc]. }
    { eapply store_ok_mono; [exact Gc | exact SOKl]. }
    { eapply store_ok_mono; [exact Gc | exact SOKa]. }
    { eapply store_ok_mono; [exact Gc|]. apply SUB; [rewrite at_u by (rewrite UspB; lia); rewrite UspB; lia | rewrite at_u by (rewrite UspB; lia); rewrite UspB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    set (Md := bi_m1 Mc spB (0x8d12c : word) (Z_to_bv 64 (tot + cnt)) (getr r4 9) (getr r4 18) BI SSW alv b1 b2 b3) in *.
    assert (Pd : forall x : word, (U x < U P - 256 \/ U P - 224 <= U x)%Z -> (U x < 1966216 + 16 * q1 + 28 \/ 1966216 + 16 * q1 + 32 <= U x)%Z ->
              (U x < 1966216 + 8 \/ 1966216 + 16 <= U x)%Z -> Md x = Mc x).
    { intros x X1 X2 X3. (lazymatch goal with |- ?G => let G' := eval unfold Md, bi_m1, bi_frame in G in change_no_check G' end).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?UBL, ?USA, ?at_u by (rewrite UspB; lia); rewrite ?UspB; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (Gd : mem_grows M1 Md).
    { eapply mem_grows_trans; [exact Gc|]. (lazymatch goal with |- ?G => let G' := eval unfold Md, bi_m1, bi_frame in G in change_no_check G' end). do 6 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
    assert (S9 : getr r4 9 = SSW) by (rewrite (AG3 9%bv) by nin; rewrite (AG2 9%bv) by nin; exact B9).
    assert (S18 : getr r4 18 = Z_to_bv 64 cnt) by (rewrite (AG3 18%bv) by nin; rewrite (AG2 18%bv) by nin; exact B18).
    exists r5, Md. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; eapply msteps_trans; [exact RUN3 | exact RUN4]|].
    split.
    { apply msum_outside; [| exact Gd]. intros x Hx. unfold cpre_Wx, cpre_W, wun, ivl in Hx. rewrite Pd by lia. rewrite Pc by lia. rewrite Pb by lia. apply Pa; lia. }
    split; [exact E1|]. split; [exact E2|]. split; [exact E10|]. split; [exact E11|]. split; [exact E8|]. split; [exact E9|].
    split; [rewrite (AG4 19%bv) by nin; rewrite (AG3 19%bv) by nin; rewrite (AG2 19%bv) by nin; exact B19|].
    split; [rewrite (AG4 20%bv) by nin; rewrite (AG3 20%bv) by nin; rewrite (AG2 20%bv) by nin; exact B20|].
    split; [rewrite (AG4 21%bv) by nin; rewrite (AG3 21%bv) by nin; rewrite (AG2 21%bv) by nin; exact B21|].
    split; [rewrite (AG4 23%bv) by nin; rewrite (AG3 23%bv) by nin; rewrite (AG2 23%bv) by nin; rewrite (AG1 23%bv) by nin; exact A23|].
    split.
    { intros k v Hin. rewrite <- S9, <- S18 in Hin. (lazymatch goal with |- ?G => let G' := eval unfold Md, bi_m1 in G in change_no_check G' end).
      assert (K : (-32 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite !rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?UBL, ?USA, ?at_u by (rewrite UspB; lia); rewrite ?UspB; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia.
      (lazymatch goal with |- ?G => let G' := eval unfold bi_frame in G in change_no_check G' end). cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin. }
    assert (THRUd : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z -> (U P - 224 <= U a)%Z -> rdn BSEGS Mc a n = Some v -> rdn BSEGS Md a n = Some v).
    { intros a n v X0 X1 Hr. rewrite <- Hr. apply rdn_ext; [exact X0|]. intros x Hx. apply Pd; lia. }
    assert (THRUcd : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z -> (U P - 200 <= U a)%Z -> rdn BSEGS Mb a n = Some v -> rdn BSEGS Md a n = Some v).
    { intros a n v X0 X1 Hr. apply THRUd; [exact X0 | lia|]. rewrite <- Hr. apply rdn_ext; [exact X0|]. intros x Hx. apply Pc; lia. }
    split.
    { apply THRUd; [rewrite at_u by (rewrite UspA; lia); rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UspA; lia); rewrite UspA; lia|].
      (lazymatch goal with |- ?G => let G' := eval unfold Mc, sa_tmem in G in change_no_check G' end). rewrite rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by (rewrite UspA; lia); rewrite ?UspA; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia.
      (lazymatch goal with |- ?G => let G' := eval unfold Mb, sa_smem in G in change_no_check G' end). do 6 (rewrite rdn_wbytes_out; [| wd_lenlit; rewrite ?length_N_to_le_bytes, ?Uc0, ?Uc1, ?Upk, ?USS, ?at_u by (rewrite UspA; lia); rewrite ?UspA; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia ..]). rd8_chain. }
    split.
    { apply THRUd; [rewrite at_u by (rewrite UspA; lia); rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UspA; lia); rewrite UspA; lia|].
      (lazymatch goal with |- ?G => let G' := eval unfold Mc, sa_tmem in G in change_no_check G' end). rewrite rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by (rewrite UspA; lia); rewrite ?UspA; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia.
      (lazymatch goal with |- ?G => let G' := eval unfold Mb, sa_smem in G in change_no_check G' end). do 6 (rewrite rdn_wbytes_out; [| wd_lenlit; rewrite ?length_N_to_le_bytes, ?Uc0, ?Uc1, ?Upk, ?USS, ?at_u by (rewrite UspA; lia); rewrite ?UspA; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia ..]). rd8_chain. }
    split.
    { intros k v Hin.
      assert (K : (-56 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply THRUcd; [rewrite at_u by (rewrite UspS; lia); rewrite UspS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UspS; lia); rewrite UspS; lia|].
      transitivity (rdn BSEGS Ma (at_ spS k) 8).
      { apply rdn_ext; [rewrite at_u by (rewrite UspS; lia); rewrite UspS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by (rewrite UspS; lia). rewrite UspS in Hx. cbn in Hx. apply Pb; lia. }
      transitivity (rdn BSEGS (st_frame M1 spS (0x8f234 : word) nd nd b (getr r1 19) (getr r1 20) (getr r1 21)) (at_ spS k) 8).
      { apply rdn_ext; [rewrite at_u by (rewrite UspS; lia); rewrite UspS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by (rewrite UspS; lia). rewrite UspS in Hx. cbn in Hx.
        (lazymatch goal with |- ?G => let G' := eval unfold Ma, st_m1 in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?Upk, ?at_u by (rewrite UspS; lia); rewrite ?UspS; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
      rewrite <- A21 in Hin. (lazymatch goal with |- ?G => let G' := eval unfold st_frame in G in change_no_check G' end). cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin. }
    split.
    { apply THRUd; [rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UspA; lia|]. (lazymatch goal with |- ?G => let G' := eval unfold Mc, sa_tmem in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite UspA. lia. }
    split.
    { apply THRUcd; [rewrite Upk; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Upk; lia|]. (lazymatch goal with |- ?G => let G' := eval unfold Mb, sa_smem in G in change_no_check G' end).
      rewrite rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?Upk, ?USS; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia.
      apply rdn_wbytes_hit8. rewrite Upk. lia. }
    split.
    { transitivity (rdn BSEGS Mb SSW 8).
      { apply rdn_ext; [rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite USS in Hx. cbn in Hx. rewrite Pd by lia. apply Pc; lia. }
      (lazymatch goal with |- ?G => let G' := eval unfold Mb, sa_smem in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite USS. lia. }
    assert (THRUbd : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z -> (1966216 + 16 <= U a)%Z -> (U a + Z.of_nat n <= 2 ^ 32)%Z ->
              (U a + Z.of_nat n <= 1966216 + 16 * q1 + 28 \/ 1966216 + 16 * q1 + 32 <= U a)%Z -> rdn BSEGS Mb a n = Some v -> rdn BSEGS Md a n = Some v).
    { intros a n v X0 X1 X2 X3 Hr. rewrite <- Hr. apply rdn_ext; [exact X0|]. intros x Hx. rewrite Pd by lia. apply Pc; lia. }
    split.
    { apply THRUbd; [rewrite Uc0; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Uc0; lia | rewrite Uc0; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Uc0; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. (lazymatch goal with |- ?G => let G' := eval unfold Mb, sa_smem in G in change_no_check G' end).
      do 4 (rewrite rdn_wbytes_out; [| wd_lenlit; rewrite ?length_N_to_le_bytes, ?Uc0, ?Uc1, ?Upk, ?USS; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia ..]).
      apply (rdn_wbytes_hit BSEGS (LE4 (v_add (Z_to_bv 64 so0) (Z_to_bv 64 inf)))). rewrite Uc0. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    split.
    { apply THRUbd; [rewrite Uc1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Uc1; lia | rewrite Uc1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Uc1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. (lazymatch goal with |- ?G => let G' := eval unfold Mb, sa_smem in G in change_no_check G' end).
      do 2 (rewrite rdn_wbytes_out; [| wd_lenlit; rewrite ?length_N_to_le_bytes, ?Uc0, ?Uc1, ?Upk, ?USS; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia ..]).
      apply (rdn_wbytes_hit BSEGS (LE4 (v_add (Z_to_bv 64 so1) (Z_to_bv 64 (cnt - inf))))). rewrite Uc1. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    split; [exact EQ1|]. split; [exact INF|].
    apply (regs_agree_trans _ r1 r2); [ra_pc AG1|]. apply (regs_agree_trans _ r2 r3); [ra_pc AG2|]. apply (regs_agree_trans _ r3 r4); [ra_pc AG3 | ra_pc AG4].
  Qed.
End CPREX.
End FPGen.
End BoDepotRunC2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotLock OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3.BoDepotAlloc BoDepotAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotBlk OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunH OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunS OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI.   (* [comment removed for export] *)
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition cpost_W (P nd b : word) (qs dstz n : Z) : Z -> Prop :=
  wun (ivl (1966216 + 16 * qs + 16) 8) (wun (ivl (1966216 + 16 * qs + 28) 1) (wun (ivl dstz n) (wun (ivl (1966216 + 16 * qs + 24) 4)
    (wun (ivl (U P - 136) 8) (tail_W P nd b))))).

Section CPOST.
  Variables (MB rom : word -> option byte) (P ra nd b newblk tr CF t3 t4 : word) (hd idz sz tag start so pk : Z) (bs : list byte).
  Variables (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v : word).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation Q := (at_ P (-112)).
  #[local] Abbreviation spS := (at_ Q (-32)).
  #[local] Abbreviation packp := (at_ Q (-24)).
  #[local] Abbreviation args := (at_ P (-104)).
  #[local] Abbreviation spA := (at_ spS (-64)).
  #[local] Abbreviation spB := (at_ spA (-16)).
  #[local] Abbreviation cnt := (sz + 1)%Z.
  #[local] Abbreviation qs := (start / 2 ^ 20)%Z.
  #[local] Abbreviation BI := (Z_to_bv 64 (U SSW + 16 * qs + 16)).
  #[local] Abbreviation dst := (st_dst newblk start).
  #[local] Abbreviation dstz := (U newblk + 8 * (start mod 2 ^ 20))%Z.
  Hypothesis H2 : getr regs 2 = at_ spB (-32).
  Hypothesis H8 : getr regs 8 = at_ BI 12.
  Hypothesis H9 : getr regs 9 = BI.
  Hypothesis H10 : getr regs 10 = newblk.
  Hypothesis H19 : getr regs 19 = args.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 sz.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 tag.
  Hypothesis H23 : getr regs 23 = Z_to_bv 64 idz.
  Hypothesis HP : (2 ^ 32 + 256 <= U P /\ U P + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HCF : (U CF + 244 <= 1966216)%Z.
  Hypothesis Hnd : (1966216 + 65552 <= U nd /\ U nd + 16 <= U P - 256)%Z.
  Hypothesis Hb : (1966216 + 65552 <= U b /\ U b + 4 <= U P - 256 /\ (U b + 4 <= U nd \/ U nd + 16 <= U b))%Z.
  Hypothesis Hblk : (1966216 + 65552 <= U newblk /\ U newblk + 2 ^ 23 <= U P - 256 /\ (U nd + 16 <= U newblk \/ U newblk + 2 ^ 23 <= U nd)
                     /\ (U b + 4 <= U newblk \/ U newblk + 2 ^ 23 <= U b))%Z.
  Hypothesis HtrP : (U P <= U tr /\ U tr + 8 * sz < 2 ^ 64)%Z.
  Hypothesis Hsz : (1 <= sz < 255)%Z.
  Hypothesis Htag : (0 <= tag < 256)%Z.
  Hypothesis Hhd : (0 <= hd < 2 ^ 31)%Z.
  Hypothesis Hstart : (0 <= start /\ start + sz + 1 <= 2 ^ 32)%Z.
  Hypothesis Hfit : (start mod 2 ^ 20 + sz < 2 ^ 20)%Z.
  Hypothesis Hso : (0 <= so < 2 ^ 32)%Z.
  Hypothesis Hpk : (0 <= pk /\ pk + 1 < 2 ^ 32)%Z.
  Hypothesis Hbs : length bs = Z.to_nat (8 * sz).
  Hypothesis SLbi : forall (k : Z) (v : word), In (k, v) [(-8, (0x8d12c%bv : word)); (-16, Z_to_bv 64 start); (-24, SSW); (-32, Z_to_bv 64 cnt)]%Z -> rdn BSEGS MB (at_ spB k) 8 = Some (LE8 v).
  Hypothesis Rara : rdn BSEGS MB (at_ spA (-8)) 8 = Some (LE8 (0x8cf6c : word)).
  Hypothesis Ras0 : rdn BSEGS MB (at_ spA (-16)) 8 = Some (LE8 packp).
  Hypothesis SLst : forall (k : Z) (v : word), In (k, v) [(-8, (0x8f234%bv : word)); (-16, nd); (-24, nd); (-32, b); (-40, t3); (-48, t4); (-56, Z_to_bv 64 hd)]%Z ->
                      rdn BSEGS MB (at_ spS k) 8 = Some (LE8 v).
  Hypothesis Ridx : rdn BSEGS MB spA 8 = Some (LE8 (Z_to_bv 64 start)).
  Hypothesis Rso : rdn BSEGS MB (st_cell SSW start) 4 = Some (LE4 (Z_to_bv 64 so)).
  Hypothesis Rpk : rdn BSEGS MB packp 8 = Some (LE8 (Z_to_bv 64 pk)).
  Hypothesis Rtr : rdn BSEGS MB args 8 = Some (LE8 tr).
  Hypothesis Rws : rdn BSEGS MB tr (length bs) = Some bs.
  Hypothesis Rq8 : rdn BSEGS MB (at_ Q (-8)) 8 = Some (LE8 (0x8f718 : word)).
  Hypothesis Rq16 : rdn BSEGS MB (at_ Q (-16)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Rcfp : rdn BSEGS MB (Z_to_bv 64 1072904) 8 = Some (LE8 CF).
  Hypothesis Rflag : rdn BSEGS MB (at_ CF 240) 4 = Some (LE4 (Z_to_bv 64 0)).
  Hypothesis SL : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v); (-72, s7v); (-80, s8v); (-88, s9v)]%Z ->
    rdn BSEGS MB (at_ P k) 8 = Some (LE8 v).
  Hypothesis SOKbd : store_ok BSEGS MB BI 8 = true.
  Hypothesis SOKbl : store_ok BSEGS MB (at_ BI 12) 1 = true.
  Hypothesis SOKd : store_ok BSEGS MB dst (8 + length bs) = true.
  Hypothesis SOKso : store_ok BSEGS MB (st_cell SSW start) 4 = true.
  Hypothesis SOKp : store_ok BSEGS MB packp 8 = true.
  Hypothesis SOKn : store_ok BSEGS MB nd 16 = true.
  Hypothesis SOKb : store_ok BSEGS MB b 4 = true.
  Hypothesis Hstk : store_ok BSEGS MB (at_ Q (-48)) 16 = true.

  Lemma put_c_post :
    exists r M', msteps BSEGS (mkst regs (0x8da70 : word) MB rom) (mkst r ra M' rom)
      /\ msum (cpost_W P nd b qs dstz (8 + 8 * sz)) MB M'
      /\ getr r 10 = Z_to_bv 64 idz /\ getr r 2 = P /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
      /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v
      /\ rdn BSEGS M' b 4 = Some (LE4 (Z_to_bv 64 idz))
      /\ rdn BSEGS M' (at_ nd 8) 4 = Some (LE4 (Z_to_bv 64 hd)) /\ rdn BSEGS M' (at_ nd 12) 4 = Some (LE4 (st_id start))
      /\ rdn BSEGS M' BI 8 = Some (LE8 newblk) /\ rdn BSEGS M' (at_ BI 12) 1 = Some [Z_to_bv 8 0]
      /\ rdn BSEGS M' (st_cell SSW start) 4 = Some (LE4 (v_add (Z_to_bv 64 so) (Z_to_bv 64 cnt)))
      /\ regs_agree (fun i : reg => In i put_clob) regs r.
  Proof using Hstk SOKb SOKn SOKp SOKso SOKd SOKbl SOKbd SL Rflag Rcfp Rq16 Rq8 Rws Rtr Rpk Rso Ridx SLst Ras0 Rara SLbi Hbs Hpk Hso Hfit Hstart Htag Hsz HtrP Hblk Hb Hnd HCF Hret HP H23 H21 H20 H19 H10 H9 H8 H2 bs pk tag t4 t3 CF tr.
    pose proof (u64_range P) as HPr. pose proof (u64_range nd) as Hndr. pose proof (u64_range b) as Hbr. pose proof (u64_range newblk) as Hnbr.
    pose proof (u64_range tr) as Htrr. pose proof (u64_range CF) as HCr.
    destruct HP as [P1 P2]. destruct Hnd as [ND1 ND2]. destruct Hb as (B1' & B2' & B3'). destruct Hblk as (BK1 & BK2 & BK3 & BK4).
    destruct HtrP as [T1 T2]. destruct Hstart as [T0 T32]. destruct Hpk as [PK0 PK1].
    assert (USS : U SSW = 1966216%Z) by reflexivity.
    assert (UQ : U Q = (U P - 112)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspS : U spS = (U P - 144)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Upk : U packp = (U P - 136)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Uargs : U args = (U P - 104)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspA : U spA = (U P - 208)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspB : U spB = (U P - 224)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Q20 : (0 <= qs < 2 ^ 12)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M20 : (0 <= start mod 2 ^ 20 < 2 ^ 20)%Z) by (apply Z.mod_pos_bound; lia).
    assert (UBI : U BI = (1966216 + 16 * qs + 16)%Z) by (rewrite USS; rewrite u_Z2bv by lia; reflexivity).
    assert (UBL : U (at_ BI 12) = (1966216 + 16 * qs + 28)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Lbs : Z.of_nat (length bs) = (8 * sz)%Z) by (rewrite Hbs, Z2Nat.id by lia; reflexivity).
    assert (Ucell : U (st_cell SSW start) = (1966216 + 16 * qs + 24)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite USS; rewrite u_Z2bv by lia; reflexivity).
    assert (Udst : U dst = dstz) by ((lazymatch goal with |- ?G => let G' := eval unfold st_dst in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Udst8 : U (at_ dst 8) = (dstz + 8)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Un8 : U (at_ nd 8) = (U nd + 8)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Un12 : U (at_ nd 12) = (U nd + 12)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (RO : ret_ok (0x8d12c : word) /\ ret_ok (0x8cf6c : word) /\ ret_ok (0x8cf8c : word) /\ ret_ok (0x8f234 : word)).
    { repeat split; (lazymatch goal with |- ?G => let G' := eval unfold ret_ok in G in change_no_check G' end); apply bv_eq; vm_compute; reflexivity. }
    destruct RO as (RO1 & RO2 & RO3 & RO4).
    (* [comment removed for export] *)
    destruct (bi_post MB rom spB (0x8d12c : word) (Z_to_bv 64 start) SSW (Z_to_bv 64 cnt) BI newblk regs H2 H8 H9 H10
                ltac:(rewrite UspB; lia) RO1 ltac:(rewrite UBI; lia) SOKbd SOKbl SLbi)
      as (r1 & RUN1 & A10 & A2 & A1 & A8 & A9 & A18 & AG1).
    set (M1 := bi_m2 MB BI newblk) in *.
    assert (P_1 : forall x : word, (U x < 1966216 + 16 * qs + 16 \/ 1966216 + 16 * qs + 24 <= U x)%Z -> (U x < 1966216 + 16 * qs + 28 \/ 1966216 + 16 * qs + 29 <= U x)%Z -> M1 x = MB x).
    { intros x X1 X2. (lazymatch goal with |- ?G => let G' := eval unfold M1, bi_m2 in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?UBL, ?UBI; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (G1 : mem_grows MB M1) by ((lazymatch goal with |- ?G => let G' := eval unfold M1, bi_m2 in G in change_no_check G' end); do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (T_1 : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z -> (U a + Z.of_nat n <= 1966216 + 16 * qs + 16 \/ 1966216 + 16 * qs + 29 <= U a \/ (1966216 + 16 * qs + 24 <= U a /\ U a + Z.of_nat n <= 1966216 + 16 * qs + 28))%Z ->
              rdn BSEGS MB a n = Some v -> rdn BSEGS M1 a n = Some v).
    { intros a n v X0 X1 Hr. rewrite <- Hr. apply rdn_ext; [exact X0|]. intros x Hx. apply P_1; lia. }
    (* [comment removed for export] *)
    destruct (sa_tail_cpost M1 rom spA (0x8cf6c : word) packp newblk start r1 A2 A8 A10 ltac:(rewrite UspA; lia) RO2 ltac:(lia))
      as (r2 & RUN2 & B10 & B2 & B1 & B8 & AG2).
    { apply T_1; [rewrite at_u by (rewrite UspA; lia); rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UspA; lia); rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rara]. }
    { apply T_1; [rewrite at_u by (rewrite UspA; lia); rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UspA; lia); rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Ras0]. }
    fold dst in B10. replace (Z_to_bv 64 (U newblk + 8 * (start mod 2 ^ 20))) with dst in B10 by reflexivity.
    (* [comment removed for export] *)
    destruct (st_mid M1 rom args tr dst sz tag r2 B10
                ltac:(rewrite (AG2 19%bv) by nin; rewrite (AG1 19%bv) by nin; exact H19) ltac:(rewrite (AG2 20%bv) by nin; rewrite (AG1 20%bv) by nin; exact H20)
                ltac:(rewrite (AG2 21%bv) by nin; rewrite (AG1 21%bv) by nin; exact H21) Hsz Htag ltac:(rewrite Udst; lia))
      as (r3 & RUN3 & C1 & C10 & C11 & C12 & AG3).
    { apply T_1; [rewrite Uargs; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Uargs; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rtr]. }
    { eapply store_ok_mono; [exact G1|]. eapply (store_ok_sub BSEGS MB dst _ (8 + length bs)); [rewrite Udst; lia | exact SOKd | lia | lia]. }
    set (M3 := wbytes M1 dst (LE8 (st_hdr sz tag))) in *.
    set (M4 := wbytes M3 (at_ dst 8) bs).
    assert (P_3 : forall x : word, (U x < dstz \/ dstz + 8 <= U x)%Z -> M3 x = M1 x).
    { intros x X1. (lazymatch goal with |- ?G => let G' := eval unfold M3 in G in change_no_check G' end). rewrite wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?Udst; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (P_4 : forall x : word, (U x < dstz + 8 \/ dstz + 8 + 8 * sz <= U x)%Z -> M4 x = M3 x).
    { intros x X1. (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end). rewrite wbytes_outside; rewrite ?Lbs, ?Udst8; try lia. reflexivity. }
    assert (G3 : mem_grows MB M3) by (eapply mem_grows_trans; [exact G1 | apply wbytes_grows]).
    assert (G4 : mem_grows MB M4) by (eapply mem_grows_trans; [exact G3 | apply wbytes_grows]).
    assert (T_4 : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z -> (U a + Z.of_nat n <= dstz \/ dstz + 8 + 8 * sz <= U a)%Z ->
              rdn BSEGS M1 a n = Some v -> rdn BSEGS M4 a n = Some v).
    { intros a n v X0 X1 Hr. rewrite <- Hr. apply rdn_ext; [exact X0|]. intros x Hx. rewrite P_4 by lia. apply P_3. lia. }
    destruct (both_imemcpy M3 (at_ dst 8) tr (8 * sz) bs rom r3 (0x8cf8c : word)) as (r4 & RUN4 & AG4).
    { constructor.
      - lia.
      - exact Hbs.
      - rewrite <- Rws. apply rdn_ext; [rewrite Lbs; lia|]. intros x Hx. rewrite Lbs in Hx. rewrite P_3 by lia. apply P_1; lia.
      - eapply store_ok_mono; [exact G3|]. eapply (store_ok_sub BSEGS MB dst _ (8 + length bs)); [rewrite Udst; lia | exact SOKd | rewrite Udst8, Udst; lia | rewrite Udst8, Udst; lia].
      - left. rewrite Udst8. lia.
      - lia.
      - rewrite Udst8. lia. }
    { exact RO3. } { exact C1. } { exact C10. } { exact C11. } { exact C12. }
    fold M4 in RUN4.
    (* [comment removed for export] *)
    destruct (st_post M4 rom spS (0x8f234 : word) SSW packp nd nd b t3 t4 (Z_to_bv 64 hd) start cnt so pk r4
                ltac:(rewrite (AG4 2%bv) by nin; rewrite (AG3 2%bv) by nin; exact B2)
                ltac:(rewrite (AG4 8%bv) by nin; rewrite (AG3 8%bv) by nin; exact B8)
                ltac:(rewrite (AG4 9%bv) by nin; rewrite (AG3 9%bv) by nin; rewrite (AG2 9%bv) by nin; exact A9)
                ltac:(rewrite (AG4 18%bv) by nin; rewrite (AG3 18%bv) by nin; rewrite (AG2 18%bv) by nin; exact A18)
                ltac:(rewrite UspS; lia) RO4 ltac:(lia) ltac:(lia) Hso ltac:(lia)
                ltac:(rewrite USS; split; [reflexivity | lia])
                ltac:(rewrite UspS, Upk; lia))
      as (r5 & RUN5 & D10 & D2 & D1 & D8 & D9 & D18 & D19 & D20 & D21 & AG5).
    { apply T_4; [rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. apply T_1; [rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Ridx]. }
    { apply T_4; [rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. apply T_1; [rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rso]. }
    { eapply store_ok_mono; [exact G4 | exact SOKso]. }
    { apply T_4; [rewrite Upk; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Upk; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. apply T_1; [rewrite Upk; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Upk; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rpk]. }
    { eapply store_ok_mono; [exact G4 | exact SOKp]. }
    { intros k v Hin.
      assert (K : (-56 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply T_4; [rewrite at_u by (rewrite UspS; lia); rewrite UspS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UspS; lia); rewrite UspS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
      apply T_1; [rewrite at_u by (rewrite UspS; lia); rewrite UspS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UspS; lia); rewrite UspS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (SLst k v Hin)]. }
    set (M5 := st_m5 M4 SSW packp start cnt so pk) in *.
    assert (P_5 : forall x : word, (U x < 1966216 + 16 * qs + 24 \/ 1966216 + 16 * qs + 28 <= U x)%Z -> (U x < U P - 136 \/ U P - 128 <= U x)%Z -> M5 x = M4 x).
    { intros x X1 X2. (lazymatch goal with |- ?G => let G' := eval unfold M5 in G in change_no_check G' end). apply st_m5_outside; rewrite ?Ucell, ?Upk; lia. }
    assert (G5 : mem_grows MB M5) by (eapply mem_grows_trans; [exact G4 | apply st_m5_grows]).
    assert (T_5 : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z ->
              (U a + Z.of_nat n <= 1966216 + 16 * qs + 16 \/ 1966216 + 16 * qs + 32 <= U a)%Z -> (U a + Z.of_nat n <= dstz \/ dstz + 8 + 8 * sz <= U a)%Z ->
              (U a + Z.of_nat n <= U P - 136 \/ U P - 128 <= U a)%Z -> rdn BSEGS MB a n = Some v -> rdn BSEGS M5 a n = Some v).
    { intros a n v X0 X1 X2 X3 Hr. rewrite <- Hr. apply rdn_ext; [exact X0|]. intros x Hx. rewrite P_5 by lia. rewrite P_4 by lia. rewrite P_3 by lia. apply P_1; lia. }
    assert (RpkS : rdn BSEGS M5 packp 8 = Some (LE8 (Z_to_bv 64 (pk + st_full so cnt)))) by ((lazymatch goal with |- ?G => let G' := eval unfold M5, st_m5 in G in change_no_check G' end); apply rdn_wbytes_hit8; rewrite Upk; lia).
    (* [comment removed for export] *)
    assert (NI2 : forall i : reg, In i [23] -> ~ In i [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19; 20; 21]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    destruct (put_tail M5 rom P ra nd b (st_id start) (Z_to_bv 64 hd) (Z_to_bv 64 idz) CF (pk + st_full so cnt)
                s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v r5 D2 D8 D9 D10 D18 D21
                ltac:(rewrite (AG5 23%bv) by nin; rewrite (AG4 23%bv) by nin; rewrite (AG3 23%bv) by nin; rewrite (AG2 23%bv) by nin; rewrite (AG1 23%bv) by nin; exact H23)
                ltac:(lia) Hret ltac:(lia) ltac:(lia)
                ltac:((lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); destruct (cnt + so =? 1048576)%Z; lia) ltac:(lia) RpkS)
      as (r6 & M6 & RUN6 & ST & E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & Rlink & Rsid & Rbk & AG6).
    { apply T_5; [rewrite at_u by (rewrite UQ; lia); rewrite UQ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UQ; lia); rewrite UQ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                  | rewrite at_u by (rewrite UQ; lia); rewrite UQ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UQ; lia); rewrite UQ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rq8]. }
    { apply T_5; [rewrite at_u by (rewrite UQ; lia); rewrite UQ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UQ; lia); rewrite UQ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                  | rewrite at_u by (rewrite UQ; lia); rewrite UQ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by (rewrite UQ; lia); rewrite UQ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rq16]. }
    { apply T_5; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rcfp]. }
    { apply T_5; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rflag]. }
    { eapply store_ok_mono; [exact G5|]. eapply (store_ok_sub BSEGS MB nd _ 16); [lia | exact SOKn | rewrite Un12; lia | rewrite Un12; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { eapply store_ok_mono; [exact G5|]. eapply (store_ok_sub BSEGS MB nd _ 16); [lia | exact SOKn | rewrite Un8; lia | rewrite Un8; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { eapply store_ok_mono; [exact G5 | exact SOKb]. }
    { eapply store_ok_mono; [exact G5 | exact Hstk]. }
    { intros k v Hin.
      assert (K : (-88 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply T_5; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact (SL k v Hin)]. }
    assert (T_6 : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z ->
              (U a + Z.of_nat n <= U P - 160 \/ U P - 144 <= U a)%Z -> (U a + Z.of_nat n <= U nd + 8 \/ U nd + 16 <= U a)%Z ->
              (U a + Z.of_nat n <= U b \/ U b + 4 <= U a)%Z -> rdn BSEGS M5 a n = Some v -> rdn BSEGS M6 a n = Some v).
    { intros a n v B0 X1 X2 X3 Hr. apply (msum_rdn_eq BSEGS _ M5 M6 _ _ _ ST B0); [| exact Hr]. intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold tail_W, wun, ivl in G in change_no_check G' end). lia. }
    exists r6, M6.
    split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; eapply msteps_trans; [exact RUN3|]; eapply msteps_trans; [exact RUN4|]; eapply msteps_trans; [exact RUN5 | exact RUN6]|].
    split.
    { destruct ST as [FT GT]. apply msum_outside; [| eapply mem_grows_trans; [exact G5 | exact GT]].
      intros x Hx. unfold cpost_W, wun, ivl in Hx. rewrite FT by (intros WT; apply Hx; do 5 right; exact WT).
      rewrite P_5 by lia. rewrite P_4 by lia. rewrite P_3 by lia. apply P_1; lia. }
    repeat (split; [assumption|]).
    split.
    { apply T_6; [rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
      transitivity (rdn BSEGS M1 BI 8).
      { apply rdn_ext; [rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite UBI in Hx. cbn in Hx. rewrite P_5 by lia. rewrite P_4 by lia. apply P_3. lia. }
      (lazymatch goal with |- ?G => let G' := eval unfold M1, bi_m2 in G in change_no_check G' end). rewrite rdn_wbytes_out; rewrite ?UBL, ?UBI; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. apply rdn_wbytes_hit8. rewrite UBI. lia. }
    split.
    { apply T_6; [rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
      transitivity (rdn BSEGS M1 (at_ BI 12) 1).
      { apply rdn_ext; [rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite UBL in Hx. cbn in Hx. rewrite P_5 by lia. rewrite P_4 by lia. apply P_3. lia. }
      (lazymatch goal with |- ?G => let G' := eval unfold M1, bi_m2 in G in change_no_check G' end). apply (rdn_wbytes_hit BSEGS [Z_to_bv 8 0]). rewrite UBL. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    split.
    { apply T_6; [rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
      (lazymatch goal with |- ?G => let G' := eval unfold M5, st_m5 in G in change_no_check G' end). rewrite rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?Ucell, ?Upk; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia.
      apply (rdn_wbytes_hit BSEGS (LE4 (v_add (Z_to_bv 64 so) (Z_to_bv 64 cnt)))). rewrite Ucell. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    apply (regs_agree_trans _ regs r1); [ra_pc AG1|]. apply (regs_agree_trans _ r1 r2); [ra_pc AG2|]. apply (regs_agree_trans _ r2 r3); [ra_pc AG3|].
    apply (regs_agree_trans _ r3 r4); [eapply regs_agree_mono; [| exact AG4]; intros i Hi; unfold imemcpy_clob in Hi; cbn [In] in Hi; (lazymatch goal with |- ?G => let G' := eval unfold put_clob in G in change_no_check G' end); repeat (destruct Hi as [<-|Hi]; [in_l|]); destruct Hi|].
    apply (regs_agree_trans _ r4 r5); [ra_pc AG5 | exact AG6].
  Qed.
End CPOST.
End FPGen.
