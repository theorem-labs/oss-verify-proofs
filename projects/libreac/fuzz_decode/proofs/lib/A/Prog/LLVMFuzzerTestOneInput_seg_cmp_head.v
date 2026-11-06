(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* LLVMFuzzerTestOneInput_seg_cmp_head: proves no function (kind: segment lemma).
   cmp_head, the first piece of the cmp segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput
   (lib/A/Prog/LLVMFuzzerTestOneInput_seg_cmp.v): from llvm_a_st_5fc (+0x5fc, the return of reac_decode_plain_le)
   the machine SRr-realizes the cut point cmp_q66c (+0x66c, the plain check passed) or cmp_q624 (+0x624, the head of
   the scan loop L2, the plain check refused).

   The code (offsets from DEC_A_LLVMF, map-code.md section 2, DecodeList.v:411-420):
     +0x5fc  addi s8,s8,-1
     +0x600  or a1,s8,s10
     +0x604  bne a0,a1 -> +0xa4c      refuted both ways (plain_ok: a0 = ns, s8 = 1; refused: a0 = -1, s8 = 0)
     +0x608  mv a7,s3                 a7 := out
     +0x60c  ld a6,80(s1)             a6 := nch mod 2^32 (spill slot 80)
     +0x610  mv s3,s7                 s3 := the frame
     +0x614  bgez a0 -> +0x66c        taken iff plain_ok (a0 = ns >= 0); the other arm is refuted per case
     +0x618  li a2,0 ; +0x61c mv a3,a7 ; +0x620 mv a1,a7     (the refused path, up to +0x624)

   The walk from +0x5fc to the two arms of +0x614 is the owner's (a Theorem Labs lane's first draft of the segment): the
   environment (cmp_extra), the seat, the run to +0x604, both arms of
   +0x604 refuted per plain_ok case, the run to +0x614 and its refuted arm. Changed here: the spill area is seated
   READ-ONLY (ch_spill0, cmp_spill0 with no write window), since nothing is stored in +0x5fc..+0x66c; so every run
   leaves the memory as it was (frame_of over no window), and the posts take llvm_a_st_5fc's memory facts as they
   are. The endings are new: one run_to to +0x66c (passed) or to +0x624 (refused), then the cut point by SRr_ret. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0s YI00 YO09 YM05 YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require DecodeShape Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
PaRun PaShadow PaJournal PaStep DecodeSyms DecodeList DecodeAddr DecodePa DecodeImg DecodePaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import YC1g YC1h YC1i YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require
reac_upstream_channels_cg reac_decode_plain_le_c reac_upstream_channels_c reac_frame_inspect_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import LLVMFuzzerTestOneInput_seg_cmp_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module CPlain := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_plain_le_c.
Module CChan := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_c.
Module CInsp := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_inspect_c.
Module LUpChannels := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_cg.

(* The spill area of llvm_a_st_5fc, as cmp_spill0 pins it, seated read-only: +0x5fc..+0x620 stores nothing. *)
Definition ch_spill0 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 120 0 0
   [YP09.mkChunk 32 (CVal 8 (SOff 39%nat 0));
    YP09.mkChunk 40 (CVal 8 (SOff 32%nat 0));
    YP09.mkChunk 48 (CVal 8 (SOff 42%nat 0));
    YP09.mkChunk 56 (CVal 8 (SOff 37%nat 0));
    YP09.mkChunk 64 (CVal 8 (SOff 40%nat 0));
    YP09.mkChunk 72 (CVal 8 (SOff 34%nat 0));
    YP09.mkChunk 80 (CVal 8 (SOff 38%nat 0));
    YP09.mkChunk 88 (CVal 8 (SOff 43%nat 0));
    YP09.mkChunk 112 (CVal 8 (SOff 35%nat 0))].

(* a register of a stopped state, its symbolic value computed (LLVMFuzzerTestOneInput_seg_cmp_defs.v cmp_reg, a
   Section-local tactic there) *)
Ltac ch_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict YK11.mkst] in Hr
  end.
(* the write rights of a run over read-only regions: none are asked *)
Ltac ch_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* keep the model term small after a run (a fresh name for it, its body forgotten) *)
Ltac ch_mdv :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    lazymatch mdx with
    | with_vm_backing _ _ _ => let mdv := fresh "mdv" in set (mdv := mdx) in *; clearbody mdv
    | _ => idtac end end.
(* what a run over read-only regions leaves of the memory: all of it *)
Ltac ch_frame :=
  intros (r & Hin & Ha); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Ha; lia|]); destruct Hin.

Section cmph.
Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

(* a register the seat named by its own atom reads, after a run that kept it, as the seat's register *)
Lemma ch_den : forall (regs : bvmap 5 word) extra (n : nat) (r : bv 5) v,
  Z.of_nat n = bv_unsigned r -> YK11.getr regs r = v ->
  sv_denot (@Eimg rc decode_listing PI_decode (Ereg regs extra)) (SOff n 0) = v.
Proof.
intros regs extra n r v Hn Hr. apply cmp_den_atom. rewrite (ew_Eimg_Ereg_nat regs extra n r Hn). exact Hr.
Qed.

Section body.
Context {fx : YK11.FPState}.

Lemma ch_body : forall (cx : dctx) (W5 : world decodesegs0) regs5 mem5 md5,
  @cmp_prem rc RA_LLVMF B MT ->
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_a_rom cx ->
  @llvm_a_st_5fc rc B MT cx W5
    (mkCfg (@YK11.mkst fx regs5 (w64 (DEC_A_LLVMF + 0x5fc)) mem5 (YK11.seg_rom decodesegs0)) md5) ->
  SRr decodesegs0 W5
    (mkCfg (@YK11.mkst fx regs5 (w64 (DEC_A_LLVMF + 0x5fc)) mem5 (YK11.seg_rom decodesegs0)) md5)
    (fun W' c' => @cmp_q624 rc B MT cx W' c' \/ @cmp_q66c rc B MT cx W' c').
Proof.
intros cx W5 regs5 mem5 md5 HPREM HB HR H5fc.
destruct HPREM as (HPCF & HUTR & HCELLS & HROS & HRONE & LAWS & ML & MTL & ABCMP & AFREE & LUC).
(* ---- from here to the arms of +0x614: a Theorem Labs lane's first draft of the segment, with the spill area seated
   read-only ---- *)
destruct H5fc as (fx5 & ly5 & S5 & regs5' & mem5' & md5' & res & out & mode & nch & ns &
  Hc5 & Hfrm5 & Hcore5 & Hperm5 & Hres4096 & Hout4096 & Hmle5 & Hmok5 &
  Rs3 & Rs7 & Rs5 & Rs11 & Ra0 & Rs2 & Rs4 & Rs6 & Rs8 & Rs9 & Rs10 &
  Hmode5 & Hfsh5 & Hres5 & Hout_ok & Hout_fill &
  Hsl32 & Hsl40 & Hsl48 & Hsl56 & Hsl64 & Hsl72 & Hsl80 & Hsl88 & Hsl112).
injection Hc5 as Hregs Hfpr Hfcs Hmem Hmd.
subst regs5' mem5' md5'.
assert (Hfrm : frm_zero (@fp_csr fx)) by (first [rewrite Hfcs | rewrite <- Hfcs]; exact Hfrm5).
clear Hfrm5 Hfpr Hfcs. clear fx5.
destruct Hcore5 as (HJ5 & Hfrs5 & R8 & R9 & Hsp5 & Hsp240 & Hsp32 & Rgp & Rtp & Hsaved5 &
  HF4096 & HF32 & HFpres5 & HFL5 & Hblk5 & Hgarr5).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ5 as (HAR5 & Hly5 & Hsecs5 & Hwle5 & Hio5 & Hfrsj5 & Hnev5 & Hk5 &
  J1 & J2 & J3 & J4 & Hgone5 & Hpres5 & Hstk5 & J5 & HQT5).
pose proof Hstk5 as (Hsp0al & HstkP & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
unfold DEC_LLVMF_STK in Hslo, Hpres5.
unfold dec_a_slot in Hsl32, Hsl40, Hsl48, Hsl56, Hsl64, Hsl72, Hsl80, Hsl88, Hsl112.
pose proof (cmp_ew regs5 res out (d_F cx) (d_SH cx) (dec_a_len (d_n cx)) (nch mod 2 ^ 32)
  (ns mod 2 ^ 32) mode (dec_a_olen nch ns) (nch mod 2 ^ 64) (ns mod 2 ^ 64)) as
  (A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43).
cbn zeta in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43.
set (EX := cmp_extra res out (d_F cx) (d_SH cx) (dec_a_len (d_n cx)) (nch mod 2 ^ 32)
  (ns mod 2 ^ 32) mode (dec_a_olen nch ns) (nch mod 2 ^ 64) (ns mod 2 ^ 64)) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (Eimg (Ereg regs5 EX)) n = ew (Ereg regs5 EX) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (B32 : ew (Eimg (Ereg regs5 EX)) 32%nat = w64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); exact A32).
assert (B34 : ew (Eimg (Ereg regs5 EX)) 34%nat = w64 out)
  by (rewrite EL by (unfold A_TEXT; lia); exact A34).
assert (B35 : ew (Eimg (Ereg regs5 EX)) 35%nat = w64 (d_F cx))
  by (rewrite EL by (unfold A_TEXT; lia); exact A35).
assert (B37 : ew (Eimg (Ereg regs5 EX)) 37%nat = w64 (dec_a_len (d_n cx)))
  by (rewrite EL by (unfold A_TEXT; lia); exact A37).
assert (B38 : ew (Eimg (Ereg regs5 EX)) 38%nat = w64 (nch mod 2 ^ 32))
  by (rewrite EL by (unfold A_TEXT; lia); exact A38).
assert (B39 : ew (Eimg (Ereg regs5 EX)) 39%nat = w64 (ns mod 2 ^ 32))
  by (rewrite EL by (unfold A_TEXT; lia); exact A39).
assert (B40 : ew (Eimg (Ereg regs5 EX)) 40%nat = w64 mode)
  by (rewrite EL by (unfold A_TEXT; lia); exact A40).
assert (B42 : ew (Eimg (Ereg regs5 EX)) 42%nat = w64 (nch mod 2 ^ 64))
  by (rewrite EL by (unfold A_TEXT; lia); exact A42).
assert (B43 : ew (Eimg (Ereg regs5 EX)) 43%nat = w64 (ns mod 2 ^ 64))
  by (rewrite EL by (unfold A_TEXT; lia); exact A43).
assert (B9 : ew (Eimg (Ereg regs5 EX)) 9%nat = YK11.getr regs5 9)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs5 EX 9%nat 9%bv eq_refl)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs5 EX)) 9%nat) = d_sp1 cx).
{ rewrite B9, R9. unfold w64. apply unsigned_lit_small. lia. }
(* the spill area is a read-only region of the seat *)
assert (HRspill : region_ok decodesegs0 (Eimg (Ereg regs5 EX)) (mrestrict (w_H W5) mem5) ch_spill0).
{ unfold ch_spill0, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp.
  split; [lia|]. split; [lia|].
  split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  - exact (cmp_chunk _ W5 mem5 39%nat (d_sp1 cx) 32 (ns mod 2 ^ 32) B39 Hsl32).
  - exact (cmp_chunk _ W5 mem5 32%nat (d_sp1 cx) 40 SHADOW_OFF B32 Hsl40).
  - exact (cmp_chunk _ W5 mem5 42%nat (d_sp1 cx) 48 (nch mod 2 ^ 64) B42 Hsl48).
  - exact (cmp_chunk _ W5 mem5 37%nat (d_sp1 cx) 56 (dec_a_len (d_n cx)) B37 Hsl56).
  - exact (cmp_chunk _ W5 mem5 40%nat (d_sp1 cx) 64 mode B40 Hsl64).
  - exact (cmp_chunk _ W5 mem5 34%nat (d_sp1 cx) 72 out B34 Hsl72).
  - exact (cmp_chunk _ W5 mem5 38%nat (d_sp1 cx) 80 (nch mod 2 ^ 32) B38 Hsl80).
  - exact (cmp_chunk _ W5 mem5 43%nat (d_sp1 cx) 88 (ns mod 2 ^ 64) B43 Hsl88).
  - exact (cmp_chunk _ W5 mem5 35%nat (d_sp1 cx) 112 (d_F cx) B35 Hsl112). }
assert (HGf : facts_ok (Eimg (Ereg regs5 EX)) cmp_facts0).
{ unfold facts_ok, cmp_facts0.
  cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  split; [|split; [|exact I]].
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
    split; [lia|]. split; [change (2 ^ 5) with 32; exact Hsp32 | lia].
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B32.
    unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    split; [unfold SHADOW_OFF; lia|]. split; [reflexivity | lia]. }
assert (HS : st_ok_pi pa_segs pa_val (Eimg (Ereg regs5 EX))
               (mkSS 0x5fc sr_atoms [ch_spill0] None cmp_facts0)
               (restrict (w_H W5) (YK11.mkst regs5 (Z_to_bv 64 (pa_val A_TEXT + 0x5fc)) mem5
                  (YK11.seg_rom pa_segs)))).
{ rewrite restrict_mkst_fx.
  apply (pa_entry_st_ok_full (PI := PI_decode)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HRspill | apply Forall_nil].
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - exact HGf. }
pose proof (Eimg_env (Ereg regs5 EX)) as HEI.
assert (SHOK : sh_ok pa_segs (SOff 32%nat 0) (@nil shent) (Eimg (Ereg regs5 EX))
                 (mrestrict (w_H W5) mem5)) by apply Forall_nil.
change (w64 (DEC_A_LLVMF + 0x5fc)) with (Z_to_bv 64 (pa_val A_TEXT + 0x5fc)).
change decodesegs0 with pa_segs.
paj_run_tok (paj_run (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) HS HJ5 SHOK Bspan; [ch_awr |].
rename ms into ms1. ch_mdv.
assert (HM1 : forall a, ms_mem ms1 a = mem5 a) by (intros x; apply HF; ch_frame).
clear HF HFr HG.
(* +0x604, the plain-result check `bne a0, (s8 - 1) | s10`: never taken.  With the plain check passed
   a0 = ns and s8 = 1, so the right side is 0 | ns = ns; with it refused a0 = -1 and s8 = 0, so the right
   side is (2 ^ 64 - 1) | ns = 2 ^ 64 - 1. *)
pose proof Hmode5 as (Hmodecell & Hnchr & Hnsr & Hvm4 & Hvm8).
assert (B10 : ew (Eimg (Ereg regs5 EX)) 10%nat = YK11.getr regs5 10)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs5 EX 10%nat 10%bv eq_refl)).
assert (B24 : ew (Eimg (Ereg regs5 EX)) 24%nat = YK11.getr regs5 24)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs5 EX 24%nat 24%bv eq_refl)).
assert (B26 : ew (Eimg (Ereg regs5 EX)) 26%nat = YK11.getr regs5 26)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs5 EX 26%nat 26%bv eq_refl)).
destruct (CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns) eqn:HP.
- (* the plain decode produced the braid: the comparison runs *)
  rewrite ?HP in Ra0, Rs8, Hout_ok; cbv iota in Ra0, Rs8; specialize (Hout_ok eq_refl).
  destruct (cmp_plain_pos _ _ _ _ HP) as (Hnch0 & Hns0 & Hprod).
  psrr_branch_tok (paj_run (SK := dec_A_sink_head) (PI := PI_decode) B LAWS)
                  (paj_branch (PI := PI_decode)) HS SHOK Bspan.
  + exfalso.
    rewrite branch_ne_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
    rewrite !U_SOff, B10, B24, B26, Ra0, Rs8, Rs10 in Hc.
    unfold w64 in Hc. rewrite !Z_to_bv_unsigned in Hc.
    unfold bv_wrap, bv_modulus, zcanon, M64 in Hc. cbn [Z.of_N] in Hc.
    assert (Hm : ns mod 2 ^ 64 = ns) by (apply Z.mod_small; lia).
    rewrite ?Hm, ?Z.add_0_r, ?Hm in Hc.
    change ((1 mod 2 ^ 64 + -1) mod 2 ^ 64) with 0 in Hc.
    rewrite Z.lor_0_l, ?Hm in Hc.
    rewrite Z.eqb_refl in Hc. discriminate Hc.
  + (* +0x608 .. +0x614 *)
    paj_run_tok (paj_run (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) HS HJ5 SHOK Bspan; [ch_awr |].
    rename ms into ms2. ch_mdv.
    assert (HM2 : forall a, ms_mem ms2 a = mem5 a) by (intros x; rewrite <- (HM1 x); apply HF; ch_frame).
    clear HF HFr HG HM1.
    psrr_branch_tok (paj_run (SK := dec_A_sink_head) (PI := PI_decode) B LAWS)
                    (paj_branch (PI := PI_decode)) HS SHOK Bspan.
    * (* +0x614 taken: a0 = ns >= 0, on to +0x66c *)
      paj_run_to_tok (paj_run_to (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) HS HJ5 SHOK Bspan 0x66c;
        [ch_awr |].
      rename ms into ms3. ch_mdv.
      assert (HM3 : forall a, ms_mem ms3 a = mem5 a) by (intros x; rewrite <- (HM2 x); apply HF; ch_frame).
      clear HF HFr HG HM2.
      (* ---- +0x66c: cmp_q66c ---- *)
      assert (EM : ms_mem ms3 = mem5) by (apply functional_extensionality; exact HM3).
      ch_reg HS (2%bv : bv 5) P2. ch_reg HS (3%bv : bv 5) P3. ch_reg HS (4%bv : bv 5) P4.
      ch_reg HS (8%bv : bv 5) P8. ch_reg HS (9%bv : bv 5) P9. ch_reg HS (10%bv : bv 5) P10.
      ch_reg HS (16%bv : bv 5) P16. ch_reg HS (17%bv : bv 5) P17. ch_reg HS (19%bv : bv 5) P19.
      ch_reg HS (20%bv : bv 5) P20. ch_reg HS (21%bv : bv 5) P21. ch_reg HS (26%bv : bv 5) P26.
      ch_reg HS (27%bv : bv 5) P27.
      pmkst HS.
      rewrite EM in HJ5 |- *.
      apply SRr_ret. cbv beta. right.
      unfold cmp_q66c.
      exists fx, ly5, S5, (ms_regs ms3), mem5. eexists. exists res, out, mode, nch, ns.
      split; [reflexivity|].
      split; [exact Hfrm|].
      split.
      { unfold dec_a_core.
        refine (conj HJ5 (conj Hfrs5 (conj _ (conj _ (conj _ (conj Hsp240 (conj Hsp32 (conj _ (conj _
          (conj Hsaved5 (conj HF4096 (conj HF32 (conj HFpres5 (conj HFL5 (conj Hblk5 Hgarr5))))))))))))))).
        - rewrite P8. exact (ch_den regs5 EX 8 8%bv _ eq_refl R8).
        - rewrite P9. exact (ch_den regs5 EX 9 9%bv _ eq_refl R9).
        - unfold spZ in Hsp5 |- *. rewrite P2, (ch_den regs5 EX 2 2%bv _ eq_refl eq_refl). exact Hsp5.
        - rewrite P3. exact (ch_den regs5 EX 3 3%bv _ eq_refl Rgp).
        - rewrite P4. exact (ch_den regs5 EX 4 4%bv _ eq_refl Rtp). }
      split; [exact Hperm5|].
      split; [exact Hres4096|]. split; [exact Hout4096|].
      split; [exact Hmle5|]. split; [exact Hmok5|].
      split; [exact HP|].
      split.
      { unfold dec_a_fr.
        split; [rewrite P19; exact (ch_den regs5 EX 23 23%bv _ eq_refl Rs7)|].
        split; [rewrite P21; exact (ch_den regs5 EX 21 21%bv _ eq_refl Rs5)|].
        rewrite P27; exact (ch_den regs5 EX 27 27%bv _ eq_refl Rs11). }
      split; [rewrite P10; exact (ch_den regs5 EX 10 10%bv _ eq_refl Ra0)|].
      split; [rewrite P16; apply cmp_den_atom; exact B38|].
      split; [rewrite P17; exact (ch_den regs5 EX 19 19%bv _ eq_refl Rs3)|].
      split; [rewrite P20; exact (ch_den regs5 EX 20 20%bv _ eq_refl Rs4)|].
      split; [rewrite P26; exact (ch_den regs5 EX 26 26%bv _ eq_refl Rs10)|].
      split; [exact Hmode5|]. split; [exact Hfsh5|]. split; [exact Hres5|]. split; [exact Hout_ok|].
      split; [exact Hsl32|]. split; [exact Hsl40|]. split; [exact Hsl48|]. split; [exact Hsl56|].
      split; [exact Hsl64|]. split; [exact Hsl72|]. split; [exact Hsl80|]. split; [exact Hsl88|].
      exact Hsl112.
    * exfalso. rewrite cmp_bge in Hc0. cbn [sv_denot] in Hc0.
      rewrite B10, Ra0, Z.add_0_r in Hc0. unfold w64 in Hc0.
      rewrite Z_to_bv_bv_unsigned in Hc0.
      rewrite !cmp_signed_lit in Hc0 by lia.
      apply Bool.negb_false_iff, Z.ltb_lt in Hc0. lia.
- (* the plain decode refused: the buffer still holds the 0xa5 fill *)
  rewrite ?HP in Ra0, Rs8, Hout_fill; cbv iota in Ra0, Rs8; specialize (Hout_fill eq_refl).
  psrr_branch_tok (paj_run (SK := dec_A_sink_head) (PI := PI_decode) B LAWS)
                  (paj_branch (PI := PI_decode)) HS SHOK Bspan.
  + exfalso.
    rewrite branch_ne_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
    rewrite !U_SOff, B10, B24, B26, Ra0, Rs8, Rs10 in Hc.
    unfold w64 in Hc. rewrite !Z_to_bv_unsigned in Hc.
    unfold bv_wrap, bv_modulus, zcanon, M64 in Hc. cbn [Z.of_N] in Hc.
    assert (Hb : 0 <= ns mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    assert (Hmm : (ns mod 2 ^ 64) mod 2 ^ 64 = ns mod 2 ^ 64) by (apply Z.mod_mod; lia).
    rewrite ?Z.add_0_r, ?Hmm in Hc.
    change ((0 mod 2 ^ 64 + -1) mod 2 ^ 64) with (2 ^ 64 - 1) in Hc.
    change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) in Hc.
    rewrite (cmp_lor_ones (ns mod 2 ^ 64) Hb) in Hc.
    rewrite (Z.mod_small (2 ^ 64 - 1) (2 ^ 64)) in Hc by lia.
    rewrite Z.eqb_refl in Hc. discriminate Hc.
  + (* +0x608 .. +0x614 *)
    paj_run_tok (paj_run (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) HS HJ5 SHOK Bspan; [ch_awr |].
    rename ms into ms2. ch_mdv.
    assert (HM2 : forall a, ms_mem ms2 a = mem5 a) by (intros x; rewrite <- (HM1 x); apply HF; ch_frame).
    clear HF HFr HG HM1.
    psrr_branch_tok (paj_run (SK := dec_A_sink_head) (PI := PI_decode) B LAWS)
                    (paj_branch (PI := PI_decode)) HS SHOK Bspan.
    * exfalso. rewrite cmp_bge in Hc0. cbn [sv_denot] in Hc0.
      rewrite B10, Ra0, Z.add_0_r in Hc0. unfold w64 in Hc0.
      rewrite Z_to_bv_bv_unsigned in Hc0.
      rewrite !cmp_signed_lit in Hc0 by lia.
      cbn in Hc0. discriminate Hc0.
    * (* +0x614 not taken: a0 = -1, on to the scan loop's head *)
      paj_run_to_tok (paj_run_to (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) HS HJ5 SHOK Bspan 0x624;
        [ch_awr |].
      rename ms into ms3. ch_mdv.
      assert (HM3 : forall a, ms_mem ms3 a = mem5 a) by (intros x; rewrite <- (HM2 x); apply HF; ch_frame).
      clear HF HFr HG HM2.
      (* ---- +0x624: cmp_q624 ---- *)
      assert (EM : ms_mem ms3 = mem5) by (apply functional_extensionality; exact HM3).
      ch_reg HS (2%bv : bv 5) P2. ch_reg HS (3%bv : bv 5) P3. ch_reg HS (4%bv : bv 5) P4.
      ch_reg HS (8%bv : bv 5) P8. ch_reg HS (9%bv : bv 5) P9. ch_reg HS (10%bv : bv 5) P10.
      ch_reg HS (11%bv : bv 5) P11. ch_reg HS (12%bv : bv 5) P12. ch_reg HS (13%bv : bv 5) P13.
      ch_reg HS (17%bv : bv 5) P17. ch_reg HS (18%bv : bv 5) P18. ch_reg HS (19%bv : bv 5) P19.
      ch_reg HS (20%bv : bv 5) P20. ch_reg HS (21%bv : bv 5) P21. ch_reg HS (25%bv : bv 5) P25.
      ch_reg HS (27%bv : bv 5) P27.
      pmkst HS.
      rewrite EM in HJ5 |- *.
      apply SRr_ret. cbv beta. left.
      unfold cmp_q624.
      exists fx, ly5, S5, (ms_regs ms3), mem5. eexists. exists res, out, mode, nch, ns.
      split; [reflexivity|].
      split; [exact Hfrm|].
      split.
      { unfold dec_a_core.
        refine (conj HJ5 (conj Hfrs5 (conj _ (conj _ (conj _ (conj Hsp240 (conj Hsp32 (conj _ (conj _
          (conj Hsaved5 (conj HF4096 (conj HF32 (conj HFpres5 (conj HFL5 (conj Hblk5 Hgarr5))))))))))))))).
        - rewrite P8. exact (ch_den regs5 EX 8 8%bv _ eq_refl R8).
        - rewrite P9. exact (ch_den regs5 EX 9 9%bv _ eq_refl R9).
        - unfold spZ in Hsp5 |- *. rewrite P2, (ch_den regs5 EX 2 2%bv _ eq_refl eq_refl). exact Hsp5.
        - rewrite P3. exact (ch_den regs5 EX 3 3%bv _ eq_refl Rgp).
        - rewrite P4. exact (ch_den regs5 EX 4 4%bv _ eq_refl Rtp). }
      split; [exact Hperm5|].
      split; [exact Hres4096|]. split; [exact Hout4096|].
      split; [exact Hmle5|]. split; [exact Hmok5|].
      split; [exact HP|].
      split.
      { unfold dec_a_fr.
        split; [rewrite P19; exact (ch_den regs5 EX 23 23%bv _ eq_refl Rs7)|].
        split; [rewrite P21; exact (ch_den regs5 EX 21 21%bv _ eq_refl Rs5)|].
        rewrite P27; exact (ch_den regs5 EX 27 27%bv _ eq_refl Rs11). }
      split; [rewrite P10; exact (ch_den regs5 EX 10 10%bv _ eq_refl Ra0)|].
      split; [rewrite P11; exact (ch_den regs5 EX 19 19%bv _ eq_refl Rs3)|].
      split; [rewrite P13; exact (ch_den regs5 EX 19 19%bv _ eq_refl Rs3)|].
      split; [rewrite P17; exact (ch_den regs5 EX 19 19%bv _ eq_refl Rs3)|].
      split; [rewrite P12; reflexivity|].
      split; [rewrite P18; exact (ch_den regs5 EX 18 18%bv _ eq_refl Rs2)|].
      split; [rewrite P20; exact (ch_den regs5 EX 20 20%bv _ eq_refl Rs4)|].
      split; [rewrite P25; exact (ch_den regs5 EX 25 25%bv _ eq_refl Rs9)|].
      split; [exact Hmode5|]. split; [exact Hfsh5|]. split; [exact Hres5|]. split; [exact Hout_fill|].
      split; [exact Hsl40|]. split; [exact Hsl56|]. split; [exact Hsl72|].
      exact Hsl112.
Qed.

End body.

Lemma cmp_head : @cmp_prem rc RA_LLVMF B MT -> forall (cx : dctx) (W : world decodesegs0) (c : config),
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_a_rom cx -> @llvm_a_st_5fc rc B MT cx W c ->
  SRr decodesegs0 W c (fun W' c' => @cmp_q624 rc B MT cx W' c' \/ @cmp_q66c rc B MT cx W' c').
Proof.
intros HPREM cx W c HB HR H5fc.
pose proof H5fc as H5fcc.
destruct H5fcc as (fx5 & ly5 & S5 & regs5 & mem5 & md5 & res & out & mode & nch & ns & Hc5 & _).
subst c.
exact (@ch_body fx5 cx W regs5 mem5 md5 HPREM HB HR H5fc).
Qed.

End cmph.
