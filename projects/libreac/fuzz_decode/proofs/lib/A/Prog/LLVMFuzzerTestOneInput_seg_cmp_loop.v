(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* LLVMFuzzerTestOneInput_seg_cmp_loop: the true path of the cmp segment of the image-A walk of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput, cmp_cmp : from cmp_q66c (+0x66c, the plain check passed) the machine SRr-realizes
   cmp_q734 (+0x734) (lib/A/Prog/LLVMFuzzerTestOneInput_seg_cmp.v).

   The code (offsets from DEC_A_LLVMF, lib/A/Prog/DecodeList.v:439-468, map-code.md section 2): +0x66c
   `addi a1,s4,50; sd a1,64(s1)`, +0x674 `blez a0` (a0 = ns > 0), +0x678 `ld a0,48(s1)` (nch), +0x67c `blez a0`,
   +0x680..+0x68c `sd s4,8(s1); sd s11,16(s1); sd s5,24(s1); sd s3,48(s1)`, +0x690..+0x6bc the register setup of
   the double loop (s3 := 0, s10 := 0, s5 := 3*nch, s6 := s4 := 3*ns, s7 := out, s2 := res + 50), +0x6c0
   `ld a0,88(s1); blez a0` (ns), +0x6c8..+0x6dc (s11 := out + 3*ns, s8 := s7, s9 := s2), the inner head +0x6e0.

   How it is proved. One seat at +0x66c (registers as atoms, the spill area as cmp_spill0, cmp_facts0: the
   defs file's seat at +0x5fc, moved), three token runs, each up to a `blez` whose taken arm is refuted (its register
   is an atom holding ns or nch, both positive by plain_ok), then a run to +0x6e0. The runs write only the spill
   area [s1, s1 + 120) (kept_of_frame), so the memory agrees with the +0x66c one outside it; the registers at
   +0x6e0 are read off the final symbolic state and its region gives the twelve slots. That is cmp_inv at
   (c, k) = (0, 0); SRr_loopZ (lib/Reusable/YA0n.v:95) with the measure nch*ns - (c*ns + k) and
   LLVMFuzzerTestOneInput_seg_cmp_after.v's cmp_l34_body as one turn reaches cmp_x734, and
   LLVMFuzzerTestOneInput_seg_cmp_x734.v's cmp_x734_q734 turns that into cmp_q734.

   Steps follow LLVMFuzzerTestOneInput_seg_cmp_scan.v (the scan loop L2 of this segment) and libreac/fuzz_boxreg's
   ReadName.v (pb_read_name, 1d92330b7ad: paj_run_tok, psrr_branch_tok, rn_kupd, field_of_region). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import LLVMFuzzerTestOneInput_seg_cmp_x734.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import LLVMFuzzerTestOneInput_seg_cmp_after.
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
(* YC4b / YC1i switch lia's division handling off for their importers; the walk's alignment facts need it
   (ReadName.v:149's line). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* The write rights of the spill area (the journal's own stack window gives them). *)
Ltac cl_awr sp1 sp0 Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
  [ reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; unfold DEC_LLVMF_STK; lia | cbn [YP09.r_whi]; lia
  | apply awr_ok_nil ].
(* The model term after a run, named and opaque. *)
Ltac cl_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    let mdv := fresh "mdv" in set (mdv := mdx) in *; clearbody mdv end.
(* After a run: the bytes outside the spill area [sp1, sp1 + 120) are the base memory's (KR), and every byte present
   in the base memory is still present (GR) (ReadName.v rn_kupd). *)
Ltac cl_kupd sp1 Usp KR GR :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rsx (mrestrict ?H ?m0) (mrestrict ?H ?m1),
    HG : mem_grows (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
    lazymatch type of KR with forall a, _ -> _ -> aview _ ?Hk _ a = aview _ _ ?mbase a =>
      let KR2 := fresh "KR" in let GR2 := fresh "GR" in
      assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 120) ->
                aview decodesegs0 Hk m1 a = aview decodesegs0 Hk mbase a);
      [ intros a Ha Hn; etransitivity;
        [ refine (kept_of_frame Ex rsx H m0 m1 (fun x => sp1 <= x < sp1 + 120) HFr _ a Ha Hn);
          intros bb wlo whi xx Hin Hr;
          let wsv := eval vm_compute in (windows rsx) in change (In (bb, wlo, whi) wsv) in Hin;
          cbn [In] in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr|]); try contradiction;
          cbv beta; first [lia | rewrite Usp in Hr; lia]
        | exact (KR a Ha Hn) ]
      | ];
      assert (GR2 : forall a, apresent Hk mbase a -> apresent Hk m1 a)
        by (intros a Ha; exact (apresent_grows H m0 m1 a HG (GR a Ha)));
      clear KR GR; rename KR2 into KR; rename GR2 into GR
    end
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Section x. Context {rc : YM05.RunCeil}.
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

(* a 64-bit value read off an atom, as a signed number *)
Lemma cl_sgn_atom : forall (E : env) n v, ew E n = w64 v -> 0 <= v < 2 ^ 63 -> bv_signed (sv_denot E (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite (cmp_den_atom E n _ Hn). unfold w64. apply cmp_signed_lit. lia.
Qed.
Lemma cl_sgn0 : forall (E : env), bv_signed (sv_denot E (SLit 0)) = 0.
Proof. intros E. reflexivity. Qed.

(* the value of an atom plus a constant *)
Lemma cl_off : forall (E : env) n v z, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 ->
  sv_denot E (SOff n z) = w64 (v + z).
Proof. intros E n v z Hn Hv Hz. rewrite denot_lit_U. unfold w64. f_equal. apply U_atom_off; [exact Hn | lia | lia]. Qed.
(* three times an atom (the `slli 1; add` triplings, as the engine leaves them) *)
Lemma cl_mul3 : forall (E : env) n v, ew E n = w64 v -> 0 <= v -> 3 * v < 2 ^ 64 ->
  sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = w64 (3 * v).
Proof.
intros E n v Hn Hv Hv3. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n v Hn) by lia. rewrite U_lit by lia.
unfold zcanon, M64. rewrite Z.mul_comm. apply Z.mod_small. lia.
Qed.
(* an atom plus three times another (the inner bound s11 at +0x6d4) *)
Lemma cl_add_mul3 : forall (E : env) n m v w, ew E n = w64 v -> ew E m = w64 w -> 0 <= v -> 0 <= w ->
  v + 3 * w < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n 0) (SMd M_MUL (SOff m 0) (SLit 3))) = w64 (v + 3 * w).
Proof.
intros E n m v w Hn Hm Hv Hw Hs. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n v Hn) by lia. rewrite (U_atom E m w Hm) by lia. rewrite U_lit by lia.
unfold zcanon, M64. rewrite (Z.mod_small (w * 3)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* a spill slot, read off a chunk of the spill-area region at s1 = atom 9 *)
Lemma cl_slot : forall (E : env) (W : world decodesegs0) mem cx lo hi wlo whi cs off e v,
  region_ok decodesegs0 E (mrestrict (w_H W) mem) (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 9%nat) = d_sp1 cx -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) off v.
Proof.
intros E W mem cx lo hi wlo whi cs off e v HR Hb Hin He Hv. unfold dec_a_slot.
apply cmp_rdword_of_val_mem; [|exact Hv].
exact (field_of_region E _ 9 (d_sp1 cx) cs lo hi wlo whi off 8%N e v HR Hb Hin He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* The taken arm of a `blez aX` whose register is the atom n holding a positive value (Wn : ew E n = w64 v):
   refuted. *)
Ltac cl_refute Wn :=
  lazymatch goal with H : branch_taken BC_GE _ (sv_denot ?Ex (SOff ?n 0)) = true |- _ =>
    exfalso; rewrite cmp_bge, cl_sgn0, (cl_sgn_atom Ex n _ Wn) in H by lia;
    apply Bool.negb_true_iff, Z.ltb_ge in H; lia
  end.
(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac cl_reg_at HS r v H tac :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : YK11.getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
Ltac cl_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* A register the run kept: KR (regs_kept_of_st_ok_pi), then the hypothesis that gives its old value. *)
Ltac cl_kept KR := etransitivity; [apply KR; cl_in | eassumption].
(* A spill slot of the final state, from its chunk e = v. *)
Ltac cl_slotp HR Hb off e v tac :=
  eapply (cl_slot _ _ _ _ _ _ _ _ _ off e v HR Hb); [cl_in | tac | first [lia | unfold SHADOW_OFF; lia]].

Section body2.
Context {fx : YK11.FPState}.

Lemma cl_body : forall (LAWS : AR_laws decodesegs0 B) (HCELLS : dec_crt_cells B)
    (ABCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc decodesegs0 B (decode_sigma DS___interceptor_trampoline_bcmp))
    (cx : dctx) ly S (W : world decodesegs0) regs mem0 md0 res out mode nch ns,
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  frm_zero (@fp_csr fx) ->
  dec_a_core B cx ly S W regs mem0 md0 dec_ev_5fc ->
  Permutation (ablocks B ly S) (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++
                                  [(out, dec_a_olen nch ns)]) ->
  4096 <= res -> 4096 <= out ->
  mo_le MT (d_S cx) S (dec_spent_5fc MT (d_n cx)) -> mo_ok MT S (dec_rest_5fc MT) ->
  CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
  dec_a_fr cx regs ->
  YK11.getr regs 10 = w64 ns ->
  YK11.getr regs 16 = w64 (nch mod 2 ^ 32) ->
  YK11.getr regs 17 = w64 out ->
  YK11.getr regs 20 = w64 res ->
  YK11.getr regs 26 = w64 (ns mod 2 ^ 64) ->
  dec_a_mode_ok cx W mem0 mode nch ns ->
  dec_a_fsh cx (aview decodesegs0 (w_H W) mem0) 0 4 ->
  garr8 decodesegs0 (mrestrict (w_H W) mem0) res (map (fun b : byte => bv_unsigned b) (d_body cx)) ->
  garr8 decodesegs0 (mrestrict (w_H W) mem0) out
    (map (fun b : byte => bv_unsigned b) (CPlain.plain_out (d_body cx) nch ns)) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem0) 32 (ns mod 2 ^ 32) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem0) 40 SHADOW_OFF ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem0) 48 (nch mod 2 ^ 64) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem0) 56 (dec_a_len (d_n cx)) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem0) 64 mode ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem0) 72 out ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem0) 80 (nch mod 2 ^ 32) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem0) 88 (ns mod 2 ^ 64) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem0) 112 (d_F cx) ->
  SRr decodesegs0 W
    (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x66c)) mem0 (YK11.seg_rom decodesegs0)) md0)
    (cmp_q734 B MT cx).
Proof.
intros LAWS HCELLS ABCMP cx ly S W regs mem0 md0 res out mode nch ns HB Hfrm Hcore Hperm Hres4096 Hout4096 Hmle Hmok
  HP Hfr R10 R16 R17 R20 R26 Hmode Hfsh Hgres Hgout S32 S40 S48 S56 S64 S72 S80 S88 S112.
destruct (cmp_plain_pos _ _ _ _ HP) as (Hnch0 & Hns0 & Hprod).
pose proof Hmode as (Hmodecell & Hnchr & Hnsr & Hvm4 & Hvm8).
pose proof Hcore as (HJ & Hfrs & R8 & R9 & Hsp & Hsp240 & Hsp32 & Rgp & Rtp & Hsaved &
  HF4096 & HF32 & HFpres & HFL & Hblk & Hgarr).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrsj & Hnev & Hk & J1 & J2 & J3 & J4 & Hgone & Hpres &
  Hstk & J5 & HQT).
pose proof Hstk as (Hsp0al & HstkP & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
unfold DEC_LLVMF_STK in Hslo, Hpres.
pose proof S32 as T32. pose proof S40 as T40. pose proof S48 as T48. pose proof S56 as T56.
pose proof S64 as T64. pose proof S72 as T72. pose proof S80 as T80. pose proof S88 as T88. pose proof S112 as T112.
unfold dec_a_slot in T32, T40, T48, T56, T64, T72, T80, T88, T112.
(* the seat's environment: the 32 registers as atoms, then cmp_extra *)
pose proof (cmp_ew regs res out (d_F cx) (d_SH cx) (dec_a_len (d_n cx)) (nch mod 2 ^ 32)
  (ns mod 2 ^ 32) mode (dec_a_olen nch ns) (nch mod 2 ^ 64) (ns mod 2 ^ 64)) as
  (A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43).
cbn zeta in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43.
set (EX := cmp_extra res out (d_F cx) (d_SH cx) (dec_a_len (d_n cx)) (nch mod 2 ^ 32)
  (ns mod 2 ^ 32) mode (dec_a_olen nch ns) (nch mod 2 ^ 64) (ns mod 2 ^ 64)) in *.
set (E := Eimg (Ereg regs EX)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs EX) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX' : forall n, (32 <= n < 44)%nat -> ew E n = ew (Ereg regs EX) n)
  by (intros n Hn; apply EL; unfold A_TEXT; lia).
rewrite <- EX' in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43 by lia.
assert (Usp : bv_unsigned (ew E 9%nat) = d_sp1 cx).
{ rewrite (ER 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
(* the spill area is a region of the seat *)
assert (HRspill : region_ok decodesegs0 E (mrestrict (w_H W) mem0) cmp_spill0).
{ unfold cmp_spill0, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp.
  split; [lia|]. split; [lia|].
  split.
  { intros o Ho. apply (apresent_writable decodesegs0). apply Hpres. lia. }
  repeat apply Forall_cons; try apply Forall_nil.
  - exact (cmp_chunk _ W mem0 39%nat (d_sp1 cx) 32 (ns mod 2 ^ 32) A39 T32).
  - exact (cmp_chunk _ W mem0 32%nat (d_sp1 cx) 40 SHADOW_OFF A32 T40).
  - exact (cmp_chunk _ W mem0 42%nat (d_sp1 cx) 48 (nch mod 2 ^ 64) A42 T48).
  - exact (cmp_chunk _ W mem0 37%nat (d_sp1 cx) 56 (dec_a_len (d_n cx)) A37 T56).
  - exact (cmp_chunk _ W mem0 40%nat (d_sp1 cx) 64 mode A40 T64).
  - exact (cmp_chunk _ W mem0 34%nat (d_sp1 cx) 72 out A34 T72).
  - exact (cmp_chunk _ W mem0 38%nat (d_sp1 cx) 80 (nch mod 2 ^ 32) A38 T80).
  - exact (cmp_chunk _ W mem0 43%nat (d_sp1 cx) 88 (ns mod 2 ^ 64) A43 T88).
  - exact (cmp_chunk _ W mem0 35%nat (d_sp1 cx) 112 (d_F cx) A35 T112). }
assert (HGf : facts_ok E cmp_facts0).
{ unfold facts_ok, cmp_facts0.
  cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  split; [|split; [|exact I]].
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
    split; [lia|]. split; [change (2 ^ 5) with 32; exact Hsp32 | lia].
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite A32.
    unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    split; [unfold SHADOW_OFF; lia|]. split; [reflexivity | lia]. }
assert (HS : st_ok_pi pa_segs pa_val E (mkSS 0x66c sr_atoms [cmp_spill0] None cmp_facts0)
               (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (pa_val A_TEXT + 0x66c)) mem0
                  (YK11.seg_rom pa_segs)))).
{ rewrite restrict_mkst_fx.
  apply (pa_entry_st_ok_full (PI := PI_decode)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HRspill | apply Forall_nil].
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - exact HGf. }
pose proof (Eimg_env (Ereg regs EX)) as HEI. fold E in HEI.
assert (SHOK : sh_ok pa_segs (SOff 32%nat 0) (@nil shent) E (mrestrict (w_H W) mem0)) by apply Forall_nil.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx <= a < d_sp1 cx + 120) ->
  aview decodesegs0 (w_H W) mem0 a = aview decodesegs0 (w_H W) mem0 a) by reflexivity.
assert (GR : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem0 a) by auto.
(* the values the run computes with: the geometry is small and positive, the blocks and the frame are below the
   allocator ceiling *)
assert (Hn32 : nch mod 2 ^ 32 = nch) by (apply Z.mod_small; lia).
assert (Hn64 : nch mod 2 ^ 64 = nch) by (apply Z.mod_small; lia).
assert (Hs32 : ns mod 2 ^ 32 = ns) by (apply Z.mod_small; lia).
assert (Hs64 : ns mod 2 ^ 64 = ns) by (apply Z.mod_small; lia).
destruct Hfr as (F19 & F21 & F27).
assert (W10 : ew E 10%nat = w64 ns) by (rewrite (ER 10%nat 10%bv eq_refl); exact R10).
assert (W16 : ew E 16%nat = w64 nch) by (rewrite (ER 16%nat 16%bv eq_refl), R16, Hn32; reflexivity).
assert (W17 : ew E 17%nat = w64 out) by (rewrite (ER 17%nat 17%bv eq_refl); exact R17).
assert (W19 : ew E 19%nat = w64 (d_F cx)) by (rewrite (ER 19%nat 19%bv eq_refl); exact F19).
assert (W20 : ew E 20%nat = w64 res) by (rewrite (ER 20%nat 20%bv eq_refl); exact R20).
assert (W21 : ew E 21%nat = w64 (d_F cx)) by (rewrite (ER 21%nat 21%bv eq_refl); exact F21).
assert (W26 : ew E 26%nat = w64 ns) by (rewrite (ER 26%nat 26%bv eq_refl), R26, Hs64; reflexivity).
assert (W27 : ew E 27%nat = w64 (d_SH cx)) by (rewrite (ER 27%nat 27%bv eq_refl); exact F27).
assert (W39 : ew E 39%nat = w64 ns) by (rewrite A39, Hs32; reflexivity).
assert (W42 : ew E 42%nat = w64 nch) by (rewrite A42, Hn64; reflexivity).
assert (W43 : ew E 43%nat = w64 ns) by (rewrite A43, Hs64; reflexivity).
assert (R2 : YK11.getr regs 2 = w64 (d_sp1 cx))
  by (unfold w64; rewrite <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hin_res : In (res, dec_a_len (d_n cx)) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; cbn; auto).
assert (Hin_out : In (out, dec_a_olen nch ns) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; cbn; auto).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_res) as (_ & _ & Hresc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_out) as (_ & _ & Houtc & _).
pose proof (cmp_plain_len _ _ _ _ HP) as Hlen.
assert (Hrq : 0 < req_size (dec_a_len (d_n cx))) by (rewrite Hlen; exact (proj1 (req_size_pos0 1492 ltac:(lia)))).
assert (Hoq : 0 < req_size (dec_a_olen nch ns))
  by (apply (fun H => proj1 (req_size_pos0 _ H)); unfold dec_a_olen; destruct ((0 <? nch) && (0 <? ns))%bool; nia).
pose proof (cmp_rdw_range W mem0 _ _ T112) as HFr64.
assert (HSH : 0 <= d_SH cx < 2 ^ 64) by (unfold d_SH, shadow_addr, SHADOW_OFF; lia).
pose proof (paj_run (fx := fx) (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUN.
pose proof (paj_run_to (fx := fx) (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_decode)) as BR.
change (w64 (DEC_A_LLVMF + 0x66c)) with (Z_to_bv 64 (pa_val A_TEXT + 0x66c)).
change decodesegs0 with pa_segs.
(* +0x66c .. +0x674: a1 := res + 50, 64(s1) := a1, up to `blez a0` *)
paj_run_tok RUN HS HJ SHOK Bspan; [cl_awr (d_sp1 cx) (d_sp0 cx) Usp |].
cl_md. cl_kupd (d_sp1 cx) Usp KR GR.
(* +0x674 `blez a0` taken (a0 = ns > 0): refuted *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ cl_refute W10. }
(* +0x678 a0 := 48(s1) = nch, up to `blez a0` at +0x67c *)
paj_run_tok RUN HS HJ SHOK Bspan; [cl_awr (d_sp1 cx) (d_sp0 cx) Usp |].
cl_md. cl_kupd (d_sp1 cx) Usp KR GR.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ cl_refute W42. }
(* +0x680 .. +0x6c4: the four stores, the register setup, a0 := 88(s1) = ns, up to `blez a0` *)
paj_run_tok RUN HS HJ SHOK Bspan; [cl_awr (d_sp1 cx) (d_sp0 cx) Usp |].
cl_md. cl_kupd (d_sp1 cx) Usp KR GR.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ cl_refute W43. }
(* +0x6c8 .. +0x6dc: the inner bound s11 = out + 3*ns, s8 := s7, s9 := s2; stop at the inner head +0x6e0 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x6e0; [cl_awr (d_sp1 cx) (d_sp0 cx) Usp |].
cl_md. cl_kupd (d_sp1 cx) Usp KR GR.
(* the state at +0x6e0: registers, the spill area, the journal *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) =>
  assert (HAE : env_agree 32 (Ereg regs EX) Ex)
    by (split; [intros nn Hnn; unfold E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs EX [2%bv; 3%bv; 4%bv; 8%bv; 9%bv]
    HS HAE ltac:(vm_compute; reflexivity)) as KRg;
  let rr0 := eval vm_compute in (nth_error (ss_mem ssx) 0) in
  lazymatch rr0 with Some ?r0 =>
    assert (HRf : region_ok decodesegs0 E (mrestrict (w_H W) (ms_mem msx)) r0)
      by exact (st_ok_pi_region_nth Ex ssx _ 0 r0 HS eq_refl) end
end.
cl_reg_at HS (19%bv : bv 5) (w64 0) Q19 ltac:(reflexivity).
cl_reg_at HS (26%bv : bv 5) (w64 0) Q26 ltac:(reflexivity).
cl_reg_at HS (21%bv : bv 5) (w64 (3 * nch)) Q21 ltac:(apply cl_mul3; [exact W16 | lia | lia]).
cl_reg_at HS (22%bv : bv 5) (w64 (3 * ns)) Q22 ltac:(apply cl_mul3; [exact W26 | lia | lia]).
cl_reg_at HS (20%bv : bv 5) (w64 (3 * ns)) Q20 ltac:(apply cl_mul3; [exact W39 | lia | lia]).
cl_reg_at HS (23%bv : bv 5) (w64 (out + 3 * ns * 0)) Q23
  ltac:(rewrite (cl_off E 17%nat out 0 W17) by lia; f_equal; lia).
cl_reg_at HS (18%bv : bv 5) (w64 (res + 50 + 3 * 0)) Q18
  ltac:(rewrite (cl_off E 20%nat res 50 W20) by lia; f_equal; lia).
cl_reg_at HS (27%bv : bv 5) (w64 (out + 3 * ns * (0 + 1))) Q27
  ltac:(rewrite (cl_add_mul3 E 34%nat 39%nat out ns A34 W39) by lia; f_equal; lia).
cl_reg_at HS (24%bv : bv 5) (w64 (out + 3 * ns * 0 + 3 * 0)) Q24
  ltac:(rewrite (cl_off E 17%nat out 0 W17) by lia; f_equal; lia).
cl_reg_at HS (25%bv : bv 5) (w64 (res + 50 + 3 * 0 + 3 * nch * 0)) Q25
  ltac:(rewrite (cl_off E 20%nat res 50 W20) by lia; f_equal; lia).
pmkst HS.
lazymatch goal with |- SRr _ ?Wx ?cx' ?Q => change (SRr decodesegs0 Wx cx' Q) end.
(* the double loop: SRr_loopZ over (c, k) with cmp_l34_body as the turn, its exit cmp_x734 turned into cmp_q734 by
   cmp_x734_q734 *)
refine (SRr_mono decodesegs0 W _ (@cmp_x734 rc B fx cx ly S W mem0 res out) (cmp_q734 B MT cx) _ _).
2: { intros W' c' _ Hx.
     exact (@cmp_x734_q734 rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI fx
       cx ly S W regs mem0 md0 res out mode nch ns W' c' LAWS HCELLS HB Hcore Hperm Hres4096
       Hout4096 Hmle Hmok Hmode Hfsh Hgres Hfrm Hx). }
refine (SRr_loopZ decodesegs0 (Z * Z) (fun x => nch * ns - (fst x * ns + snd x))
  (fun x => @cmp_inv rc B fx cx ly S W mem0 res out nch ns (fst x) (snd x))
  (@cmp_x734 rc B fx cx ly S W mem0 res out) _ (0, 0) W _ _).
{ intros x W' c' Hx.
  exact (@cmp_l34_body rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI fx
    cx ly S W regs mem0 md0 res out mode nch ns LAWS ABCMP HB Hcore Hperm Hres4096 Hout4096 Hmle Hmok HP
    Hmode Hfsh Hgres Hgout Hfrm x W' c' Hx). }
cbv beta. unfold cmp_inv. cbn [fst snd].
split; [reflexivity|]. split; [lia|]. split; [lia|].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => exists (ms_regs msx), (ms_mem msx) end.
eexists. split; [reflexivity|].
split; [exact HJ|].
split; [cl_kept KRg|]. split; [cl_kept KRg|]. split; [cl_kept KRg|].
split; [cl_kept KRg|]. split; [cl_kept KRg|].
split; [exact Q19|]. split; [exact Q26|]. split; [exact Q21|]. split; [exact Q22|]. split; [exact Q20|].
split; [exact Q23|]. split; [exact Q18|]. split; [exact Q27|]. split; [exact Q24|]. split; [exact Q25|].
split; [intros a Ha Hn; apply KR; [exact Ha | lia]|].
split; [exact GR|].
split; [cl_slotp HRf Usp 8 (SOff 20%nat 0) res ltac:(exact (cmp_den_atom E 20%nat _ W20))|].
split; [cl_slotp HRf Usp 16 (SOff 27%nat 0) (d_SH cx) ltac:(exact (cmp_den_atom E 27%nat _ W27))|].
split; [cl_slotp HRf Usp 24 (SOff 21%nat 0) (d_F cx) ltac:(exact (cmp_den_atom E 21%nat _ W21))|].
split; [cl_slotp HRf Usp 32 (SOff 39%nat 0) (ns mod 2 ^ 32) ltac:(exact (cmp_den_atom E 39%nat _ A39))|].
split; [cl_slotp HRf Usp 40 (SOff 32%nat 0) SHADOW_OFF ltac:(exact (cmp_den_atom E 32%nat _ A32))|].
split; [cl_slotp HRf Usp 48 (SOff 19%nat 0) (d_F cx) ltac:(exact (cmp_den_atom E 19%nat _ W19))|].
split; [cl_slotp HRf Usp 56 (SOff 37%nat 0) (dec_a_len (d_n cx)) ltac:(exact (cmp_den_atom E 37%nat _ A37))|].
split; [cl_slotp HRf Usp 64 (SOff 20%nat 50) (res + 50) ltac:(apply cl_off; [exact W20 | lia | lia])|].
split; [cl_slotp HRf Usp 72 (SOff 34%nat 0) out ltac:(exact (cmp_den_atom E 34%nat _ A34))|].
split; [cl_slotp HRf Usp 80 (SOff 38%nat 0) (nch mod 2 ^ 32) ltac:(exact (cmp_den_atom E 38%nat _ A38))|].
split; [cl_slotp HRf Usp 88 (SOff 43%nat 0) (ns mod 2 ^ 64) ltac:(exact (cmp_den_atom E 43%nat _ A43))|].
cl_slotp HRf Usp 112 (SOff 35%nat 0) (d_F cx) ltac:(exact (cmp_den_atom E 35%nat _ A35)).
Qed.

End body2.

Lemma cmp_cmp : @cmp_prem rc RA_LLVMF B MT -> forall (cx : dctx) (W : world decodesegs0) (c : config),
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_a_rom cx -> @cmp_q66c rc B MT cx W c -> SRr decodesegs0 W c (@cmp_q734 rc B MT cx).
Proof.
intros HPREM cx W c HB HR H66c.
destruct HPREM as (HPCF & HUTR & HCELLS & HROR & HRONE & LAWS & ML & MTL & ABCMP & AFREE & LUC).
destruct H66c as (fx' & ly' & S' & regs' & mem' & md' & res & out & mode & nch & ns & -> & Hfrm & Hcore & Hperm &
  Hres & Hout & Hmle & Hmok & HP & Hfr & R10 & R16 & R17 & R20 & R26 & Hmode & Hfsh & Hgres & Hgout &
  S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S112).
exact (@cl_body fx' LAWS HCELLS ABCMP cx ly' S' W regs' mem' md' res out mode nch ns HB Hfrm Hcore Hperm Hres Hout
  Hmle Hmok HP Hfr R10 R16 R17 R20 R26 Hmode Hfsh Hgres Hgout S32 S40 S48 S56 S64 S72 S80 S88 S112).
Qed.
End x.
