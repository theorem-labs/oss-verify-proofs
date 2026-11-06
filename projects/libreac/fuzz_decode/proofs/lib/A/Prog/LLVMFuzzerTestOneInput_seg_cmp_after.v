(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* LLVMFuzzerTestOneInput_seg_cmp_after: the second half of one turn of the bcmp double loop of the cmp segment of
   the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput (lib/A/Prog/LLVMFuzzerTestOneInput_seg_cmp.v),
   cmp_l34_after : from cmp_q6f0 (+0x6f0, the bcmp return in turn (c, k), a0 = 0) to cmp_inv at (c, k + 1) or
   (c + 1, 0) or to cmp_x734 (+0x734); and the turn cmp_l34_body = cmp_l34_call (LLVMFuzzerTestOneInput_seg_cmp_defs.v)
   then cmp_l34_after.

   The code (offsets from DEC_A_LLVMF, lib/A/Prog/DecodeList.v:472-489, map-code.md section 2): +0x6f0 `snez a0,a0`,
   +0x6f4 `addi s8,s8,3`, +0x6f8 `or s10,s10,a0`, +0x6fc `add s9,s9,s5`, +0x700 `bne s8,s11 -> +0x6e0`; +0x704
   `addi s3,s3,1`, +0x708 `addi s2,s2,3`, +0x70c `add s7,s7,s6`, +0x710 `ld a0,80(s1)` (nch), +0x714
   `bne s3,a0 -> +0x6c0`; +0x6c0 `ld a0,88(s1); blez a0` (ns), +0x6c8..+0x6dc the next channel's bound and cursors;
   +0x718..+0x72c the six reloads, +0x730 `bnez s10 -> +0xa4c`.

   How it is proved. One seat at +0x6f0 (the defs file's cmp_seat1: registers as atoms, the spill area as
   cmp_spill1), with a0 and s10 pinned to the literal 0 (st_ok_pi_pin_reg'), so the engine folds snez / or and
   decides the `bnez s10` at +0x730 itself (fall-through: the abort edge is never stepped). Token runs to each
   branch: `bne s8, s11` taken iff k + 1 <> ns (then k + 1 < ns), `bne s3, a0` taken iff c + 1 <> nch, `blez a0`
   on ns refuted. The runs store nothing; kept_of_frame keeps the memory outside [s1 - 8192, s1 + 120) equal to
   cmp_q6f0's, hence to mem5. Registers are read off the final symbolic state, slots off its region.

   Steps follow LLVMFuzzerTestOneInput_seg_cmp_loop.v / _seg_cmp_scan.v (this segment) and libreac/fuzz_boxreg's
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
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* The write rights of the spill area (the journal's own stack window gives them). *)
Ltac ca_awr sp1 sp0 Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
  [ reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; unfold DEC_LLVMF_STK; lia | cbn [YP09.r_whi]; lia
  | apply awr_ok_nil ].
(* The model term after a run, named and opaque. *)
Ltac ca_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    let mdv := fresh "mdv" in set (mdv := mdx) in *; clearbody mdv end.
(* After a run over the loop's spill picture: the bytes outside [sp1 - 8192, sp1 + 120) are still the base
   memory's (KR), and every byte present in the base memory is still present (GR) (ReadName.v rn_kupd; the main
   file's cmp_kupd, which is local to its Section). *)
Ltac ca_kupd sp1 Usp KR GR :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rsx (mrestrict ?H ?m0) (mrestrict ?H ?m1),
    HG : mem_grows (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
    lazymatch type of KR with forall a, _ -> _ -> aview _ ?Hk _ a = aview _ _ ?mbase a =>
      let KR2 := fresh "KR" in let GR2 := fresh "GR" in
      assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1 + 120) ->
                aview decodesegs0 Hk m1 a = aview decodesegs0 Hk mbase a);
      [ intros a Ha Hn; etransitivity;
        [ refine (kept_of_frame Ex rsx H m0 m1 (fun x => sp1 - 8192 <= x < sp1 + 120) HFr _ a Ha Hn);
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

(* the sum of two atoms (s9 += s5 at +0x6fc, s7 += s6 at +0x70c, as the engine leaves them) *)
Lemma ca_add2 : forall (E : env) n m v w, ew E n = w64 v -> ew E m = w64 w -> 0 <= v -> 0 <= w -> v + w < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = w64 (v + w).
Proof.
intros E n m v w Hn Hm Hv Hw Hs. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn) by lia. rewrite (U_atom E m w Hm) by lia.
unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
(* the inner bound s11 = [72(s1)] + (s4 + s6 * s3) of +0x6c8..+0x6d4, with s3 = c + 1 one up from its atom *)
Lemma ca_s11 : forall (E : env) n p m q o a b cc,
  ew E n = w64 o -> ew E p = w64 a -> ew E m = w64 b -> ew E q = w64 cc ->
  0 <= o < 2 ^ 64 -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= cc -> cc + 1 < 2 ^ 64 ->
  o + (a + b * (cc + 1)) < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n 0) (SAlu ALU_ADD (SOff p 0) (SMd M_MUL (SOff m 0) (SOff q 1))))
    = w64 (o + (a + b * (cc + 1))).
Proof.
intros E n p m q o a b cc Hn Hp Hm Hq Ho Ha Hb Hc Hc1 Hs.
assert (Hb1 : 0 <= b * (cc + 1)) by nia.
rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n o Hn) by lia. rewrite (U_atom E p a Hp) by lia. rewrite (U_atom E m b Hm) by lia.
rewrite (U_atom_off E q cc 1 Hq) by lia.
unfold zcanon, M64.
rewrite (Z.mod_small (b * (cc + 1))) by lia. rewrite (Z.mod_small (a + b * (cc + 1))) by lia.
apply Z.mod_small. lia.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ca_reg_at HS r v H tac :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : YK11.getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
Ltac ca_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* A register the run kept: KR (regs_kept_of_st_ok_pi), then the hypothesis that gives its old value. *)
Ltac ca_kept KR := etransitivity; [apply KR; ca_in | eassumption].
(* At the end of a stretch: the registers it kept (KRg) and its spill-area region (HRf). *)
Ltac ca_final HS HAE KRg HRf l :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wq) ?msx) =>
    lazymatch type of HAE with env_agree _ (Ereg ?rg ?ex) _ =>
      pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H Wq) msx) rg ex l HS HAE
        ltac:(vm_compute; reflexivity)) as KRg end;
    let rr0 := eval vm_compute in (nth_error (ss_mem ssx) 0) in
    lazymatch rr0 with Some ?r0 =>
      assert (HRf : region_ok decodesegs0 Ex (mrestrict (w_H Wq) (ms_mem msx)) r0)
        by exact (st_ok_pi_region_nth Ex ssx _ 0 r0 HS eq_refl) end
  end.
(* A spill slot of the final state whose chunk is the atom n (A : ew E n = w64 v), and the slot s1 + 64 *)
Ltac ca_slota HR Hb off n A :=
  eapply (cmp_slot _ _ _ _ _ _ _ _ _ off (SOff n 0) _ HR Hb);
  [ ca_in | exact (cmp_den_atom _ n _ A) | first [lia | unfold SHADOW_OFF; lia] ].
Ltac ca_slot64 HR Hb A :=
  eapply (cmp_slot _ _ _ _ _ _ _ _ _ 64 (SOff 33%nat 50) _ HR Hb);
  [ ca_in | apply cmp_off; [exact A | lia | lia] | lia ].
(* the twelve slots of cmp_inv, off the loop's spill picture *)
Ltac ca_slots12 HRf Usp A33 A36 A35 A39 A32 A37 A34 A38 A43 :=
  split; [ca_slota HRf Usp 8 33%nat A33|]; split; [ca_slota HRf Usp 16 36%nat A36|];
  split; [ca_slota HRf Usp 24 35%nat A35|]; split; [ca_slota HRf Usp 32 39%nat A39|];
  split; [ca_slota HRf Usp 40 32%nat A32|]; split; [ca_slota HRf Usp 48 35%nat A35|];
  split; [ca_slota HRf Usp 56 37%nat A37|]; split; [ca_slot64 HRf Usp A33|];
  split; [ca_slota HRf Usp 72 34%nat A34|]; split; [ca_slota HRf Usp 80 38%nat A38|];
  split; [ca_slota HRf Usp 88 43%nat A43|]; ca_slota HRf Usp 112 35%nat A35.

Section body2.
Context {fx : YK11.FPState}.

Lemma cmp_l34_after : forall (cx : dctx) ly5 S5 (W5 : world decodesegs0) regs5 mem5 md5 res out nch ns,
  AR_laws decodesegs0 B ->
  dec_a_core B cx ly5 S5 W5 regs5 mem5 md5 dec_ev_5fc ->
  Permutation (ablocks B ly5 S5) (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++ [(out, dec_a_olen nch ns)]) ->
  CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
  forall (c k : Z) (W : world decodesegs0) (c' : config),
    @cmp_q6f0 rc B fx cx ly5 S5 W5 mem5 res out nch ns c k W c' ->
    SRr decodesegs0 W c' (fun W2 c2 => @cmp_x734 rc B fx cx ly5 S5 W5 mem5 res out W2 c2 \/
      exists x', 0 <= nch * ns - (fst x' * ns + snd x') < nch * ns - (c * ns + k) /\
                 @cmp_inv rc B fx cx ly5 S5 W5 mem5 res out nch ns (fst x') (snd x') W2 c2).
Proof.
intros cx ly5 S5 W5 regs5 mem5 md5 res out nch ns LAWS Hcore5 Hperm5 HP c k W c' H6.
destruct H6 as (-> & Hc & Hk & regs & mem & md & -> & HJ & Rsp & Rs1 & Rs0 & Rgp & Rtp & Ra0 & Rs3 & Rs10 &
  Rs5 & Rs6 & Rs4 & Rs7 & Rs2 & Rs11 & Rs8 & Rs9 & KR & GR &
  S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S112).
pose proof Hcore5 as (HJ5 & Hfrs5 & R8 & R9 & Hsp5 & Hsp240 & Hsp32 & Rgp5 & Rtp5 & Hsaved5 &
  HF4096 & HF32 & HFpres5 & HFL5 & Hblk5 & Hgarr5).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrsj & Hnev & Hkj & J1 & J2 & J3 & J4 & Hgone & Hpres &
  Hstk & J5 & HQT).
pose proof Hstk as (Hsp0al & HstkP & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
unfold DEC_LLVMF_STK in Hslo, Hpres.
destruct (cmp_plain_pos _ _ _ _ HP) as (Hnch0 & Hns0 & Hprod).
pose proof (cmp_plain_len _ _ _ _ HP) as Hlen.
assert (Hin_res : In (res, dec_a_len (d_n cx)) (ablocks B ly5 S5))
  by (apply (Permutation_in _ (Permutation_sym Hperm5)); apply in_or_app; right; cbn; auto).
assert (Hin_out : In (out, dec_a_olen nch ns) (ablocks B ly5 S5))
  by (apply (Permutation_in _ (Permutation_sym Hperm5)); apply in_or_app; right; cbn; auto).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_res) as (_ & Hr4096 & Hresc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_out) as (_ & Ho4096 & Houtc & _).
assert (Holen : dec_a_olen nch ns = 3 * nch * ns)
  by (unfold dec_a_olen; replace ((0 <? nch) && (0 <? ns))%bool with true; [reflexivity|];
      symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
assert (Hoq : 3 * nch * ns <= req_size (dec_a_olen nch ns))
  by (rewrite Holen; apply (fun H => proj2 (req_size_pos0 _ H)); nia).
assert (Hrq : 1492 <= req_size (dec_a_len (d_n cx)))
  by (rewrite Hlen; apply (fun H => proj2 (req_size_pos0 _ H)); lia).
assert (Hnb : nch <= 480 /\ ns <= 480) by nia.
assert (M1 : 0 <= ns * c /\ ns * c + ns <= nch * ns) by nia.
assert (M2 : 0 <= nch * k /\ nch * k + nch <= nch * ns) by nia.
assert (Hn32 : nch mod 2 ^ 32 = nch) by (apply Z.mod_small; lia).
assert (Hn64 : nch mod 2 ^ 64 = nch) by (apply Z.mod_small; lia).
assert (Hs32 : ns mod 2 ^ 32 = ns) by (apply Z.mod_small; lia).
assert (Hs64 : ns mod 2 ^ 64 = ns) by (apply Z.mod_small; lia).
(* the seat at +0x6f0: registers as atoms, the spill area as cmp_spill1, a0 and s10 pinned to the literal 0 *)
pose proof (@cmp_seat1 rc fx cx W5 regs mem 0x6f0 res out 0 nch ns Rs1 ltac:(lia) Hsp32 Hsp240 Hpres
  ltac:(lia) ltac:(lia) S8 S16 S24 S32 S40 S48 S56 S64 S72 S80 S88 S112) as HS0.
pose proof (cmp_ew regs res out (d_F cx) (d_SH cx) (dec_a_len (d_n cx)) (nch mod 2 ^ 32)
  (ns mod 2 ^ 32) 0 (dec_a_olen nch ns) (nch mod 2 ^ 64) (ns mod 2 ^ 64)) as
  (A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43).
cbn zeta in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43.
set (EX := cmp_extra res out (d_F cx) (d_SH cx) (dec_a_len (d_n cx)) (nch mod 2 ^ 32)
  (ns mod 2 ^ 32) 0 (dec_a_olen nch ns) (nch mod 2 ^ 64) (ns mod 2 ^ 64)) in *.
set (E := Eimg (Ereg regs EX)) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs EX) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX' : forall n, (32 <= n < 44)%nat -> ew E n = ew (Ereg regs EX) n)
  by (intros n Hn; apply EL; unfold A_TEXT; lia).
rewrite <- EX' in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43 by lia.
assert (HAE : env_agree 32 (Ereg regs EX) E)
  by (split; [intros nn Hnn; unfold E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Usp : bv_unsigned (ew E 9%nat) = d_sp1 cx).
{ rewrite (ER 9%nat 9%bv eq_refl), Rs1. unfold w64. apply unsigned_lit_small. lia. }
lazymatch type of HS0 with st_ok_pi _ _ _ ?ss ?ms =>
  assert (Q10 : YK11.getr (ms_regs ms) 10 = Z_to_bv 64 0) by (cbn [ms_regs restrict YK11.mkst]; exact Ra0);
  pose proof (st_ok_pi_pin_reg' E ss ms 10%bv 0 HS0 Q10 eq_refl) as HS1 end.
lazymatch type of HS1 with st_ok_pi _ _ _ ?ss ?ms =>
  assert (Q26 : YK11.getr (ms_regs ms) 26 = Z_to_bv 64 0) by (cbn [ms_regs restrict YK11.mkst]; exact Rs10);
  pose proof (st_ok_pi_pin_reg' E ss ms 26%bv 0 HS1 Q26 eq_refl) as HS end.
clear HS0 HS1 Q10 Q26.
pose proof (Eimg_env (Ereg regs EX)) as HEI. fold E in HEI.
assert (SHOK : sh_ok pa_segs (SOff 32%nat 0) (@nil shent) E (mrestrict (w_H W5) mem)) by apply Forall_nil.
(* the atoms the runs compute with *)
assert (W18 : ew E 18%nat = w64 (res + 50 + 3 * c)) by (rewrite (ER 18%nat 18%bv eq_refl); exact Rs2).
assert (W19 : ew E 19%nat = w64 c) by (rewrite (ER 19%nat 19%bv eq_refl); exact Rs3).
assert (W20 : ew E 20%nat = w64 (3 * ns)) by (rewrite (ER 20%nat 20%bv eq_refl); exact Rs4).
assert (W21 : ew E 21%nat = w64 (3 * nch)) by (rewrite (ER 21%nat 21%bv eq_refl); exact Rs5).
assert (W22 : ew E 22%nat = w64 (3 * ns)) by (rewrite (ER 22%nat 22%bv eq_refl); exact Rs6).
assert (W23 : ew E 23%nat = w64 (out + 3 * ns * c)) by (rewrite (ER 23%nat 23%bv eq_refl); exact Rs7).
assert (W24 : ew E 24%nat = w64 (out + 3 * ns * c + 3 * k)) by (rewrite (ER 24%nat 24%bv eq_refl); exact Rs8).
assert (W25 : ew E 25%nat = w64 (res + 50 + 3 * c + 3 * nch * k)) by (rewrite (ER 25%nat 25%bv eq_refl); exact Rs9).
assert (W27 : ew E 27%nat = w64 (out + 3 * ns * (c + 1))) by (rewrite (ER 27%nat 27%bv eq_refl); exact Rs11).
assert (W38 : ew E 38%nat = w64 nch) by (rewrite A38, Hn32; reflexivity).
assert (W43 : ew E 43%nat = w64 ns) by (rewrite A43, Hs64; reflexivity).
(* the slot values are 64-bit numbers *)
pose proof (cmp_rdw_range W5 mem _ _ S8) as RG8. pose proof (cmp_rdw_range W5 mem _ _ S16) as RG16.
pose proof (cmp_rdw_range W5 mem _ _ S24) as RG24. pose proof (cmp_rdw_range W5 mem _ _ S56) as RG56.
pose proof (cmp_rdw_range W5 mem _ _ S64) as RG64. pose proof (cmp_rdw_range W5 mem _ _ S72) as RG72.
pose proof (cmp_rdw_range W5 mem _ _ S32) as RG32. pose proof (cmp_rdw_range W5 mem _ _ S80) as RG80.
pose proof (cmp_rdw_range W5 mem _ _ S88) as RG88.
pose proof (paj_run (fx := fx) (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUN.
pose proof (paj_run_to (fx := fx) (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_decode)) as BR.
change (w64 (DEC_A_LLVMF + 0x6f0)) with (Z_to_bv 64 (pa_val A_TEXT + 0x6f0)).
change decodesegs0 with pa_segs.
(* +0x6f0 .. +0x700: snez a0 (0), s8 += 3, s10 |= a0 (0), s9 += s5, up to `bne s8, s11` *)
paj_run_tok RUN HS HJ SHOK Bspan; [ca_awr (d_sp1 cx) (d_sp0 cx) Usp |].
ca_md. ca_kupd (d_sp1 cx) Usp KR GR.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* taken: k + 1 < ns, back to the inner head +0x6e0, cmp_inv at (c, k + 1) *)
  assert (Hk1 : k + 1 < ns).
  { lazymatch goal with H : branch_taken BC_NE _ _ = true |- _ =>
      rewrite branch_ne_U in H;
      rewrite (U_atom_off E 24%nat (out + 3 * ns * c + 3 * k) 3 W24) in H by lia;
      rewrite (U_atom E 27%nat (out + 3 * ns * (c + 1)) W27) in H by lia;
      apply negb_true_iff, Z.eqb_neq in H; lia end. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x6e0; [ca_awr (d_sp1 cx) (d_sp0 cx) Usp |].
  ca_md. ca_kupd (d_sp1 cx) Usp KR GR.
  ca_final HS HAE KRg HRf ([2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 27%bv] : list (bv 5)).
  ca_reg_at HS (26%bv : bv 5) (w64 0) Q26 ltac:(reflexivity).
  ca_reg_at HS (24%bv : bv 5) (w64 (out + 3 * ns * c + 3 * (k + 1))) Q24
    ltac:(rewrite (cmp_off E 24%nat (out + 3 * ns * c + 3 * k) 3 W24) by lia; f_equal; lia).
  ca_reg_at HS (25%bv : bv 5) (w64 (res + 50 + 3 * c + 3 * nch * (k + 1))) Q25
    ltac:(rewrite (ca_add2 E 21%nat 25%nat (3 * nch) (res + 50 + 3 * c + 3 * nch * k) W21 W25) by lia;
          f_equal; lia).
  pmkst HS.
  apply SRr_ret. cbv beta. right. exists (c, k + 1). cbn [fst snd].
  split; [lia|].
  unfold cmp_inv.
  split; [reflexivity|]. split; [lia|]. split; [lia|].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => exists (ms_regs msx), (ms_mem msx) end.
  eexists. split; [reflexivity|].
  split; [exact HJ|].
  split; [ca_kept KRg|]. split; [ca_kept KRg|]. split; [ca_kept KRg|]. split; [ca_kept KRg|]. split; [ca_kept KRg|].
  split; [ca_kept KRg|]. split; [exact Q26|].
  split; [ca_kept KRg|]. split; [ca_kept KRg|]. split; [ca_kept KRg|].
  split; [ca_kept KRg|]. split; [ca_kept KRg|]. split; [ca_kept KRg|].
  split; [exact Q24|]. split; [exact Q25|].
  split; [exact KR|]. split; [exact GR|].
  ca_slots12 HRf Usp A33 A36 A35 A39 A32 A37 A34 A38 A43.
- (* not taken: k + 1 = ns; +0x704 .. +0x714: s3 += 1, s2 += 3, s7 += s6, a0 := 80(s1) = nch, `bne s3, a0` *)
  paj_run_tok RUN HS HJ SHOK Bspan; [ca_awr (d_sp1 cx) (d_sp0 cx) Usp |].
  ca_md. ca_kupd (d_sp1 cx) Usp KR GR.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* taken: c + 1 < nch; +0x6c0 a0 := 88(s1) = ns, `blez a0` *)
    assert (Hcn : c + 1 < nch).
    { lazymatch goal with H : branch_taken BC_NE (sv_denot _ (SOff 19 1)) _ = true |- _ =>
        rewrite branch_ne_U in H; rewrite (U_atom_off E 19%nat c 1 W19) in H by lia;
        rewrite (U_atom E 38%nat nch W38) in H by lia; apply negb_true_iff, Z.eqb_neq in H; lia end. }
    assert (M3 : ns * c + 2 * ns <= nch * ns) by nia.
    paj_run_tok RUN HS HJ SHOK Bspan; [ca_awr (d_sp1 cx) (d_sp0 cx) Usp |].
    ca_md. ca_kupd (d_sp1 cx) Usp KR GR.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* `blez a0` taken: a0 = ns > 0, refuted *)
      exfalso.
      lazymatch goal with H : branch_taken BC_GE _ _ = true |- _ =>
        rewrite cmp_bge, cmp_sgn0, (cmp_sgn_atom E 43%nat ns W43) in H by lia;
        apply Bool.negb_true_iff, Z.ltb_ge in H; lia end.
    * (* +0x6c8 .. +0x6dc: s11 := out + 3*ns + 3*ns*(c + 1), s8 := s7, s9 := s2; cmp_inv at (c + 1, 0) *)
      paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x6e0; [ca_awr (d_sp1 cx) (d_sp0 cx) Usp |].
      ca_md. ca_kupd (d_sp1 cx) Usp KR GR.
      ca_final HS HAE KRg HRf ([2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 20%bv; 21%bv; 22%bv] : list (bv 5)).
      ca_reg_at HS (26%bv : bv 5) (w64 0) Q26 ltac:(reflexivity).
      ca_reg_at HS (19%bv : bv 5) (w64 (c + 1)) Q19 ltac:(apply cmp_off; [exact W19 | lia | lia]).
      ca_reg_at HS (23%bv : bv 5) (w64 (out + 3 * ns * (c + 1))) Q23
        ltac:(rewrite (ca_add2 E 22%nat 23%nat (3 * ns) (out + 3 * ns * c) W22 W23) by lia; f_equal; lia).
      ca_reg_at HS (18%bv : bv 5) (w64 (res + 50 + 3 * (c + 1))) Q18
        ltac:(rewrite (cmp_off E 18%nat (res + 50 + 3 * c) 3 W18) by lia; f_equal; lia).
      ca_reg_at HS (27%bv : bv 5) (w64 (out + 3 * ns * (c + 1 + 1))) Q27
        ltac:(rewrite (ca_s11 E 34%nat 20%nat 22%nat 19%nat out (3 * ns) (3 * ns) c A34 W20 W22 W19) by lia;
              f_equal; lia).
      ca_reg_at HS (24%bv : bv 5) (w64 (out + 3 * ns * (c + 1) + 3 * 0)) Q24
        ltac:(rewrite (ca_add2 E 22%nat 23%nat (3 * ns) (out + 3 * ns * c) W22 W23) by lia; f_equal; lia).
      ca_reg_at HS (25%bv : bv 5) (w64 (res + 50 + 3 * (c + 1) + 3 * nch * 0)) Q25
        ltac:(rewrite (cmp_off E 18%nat (res + 50 + 3 * c) 3 W18) by lia; f_equal; lia).
      pmkst HS.
      apply SRr_ret. cbv beta. right. exists (c + 1, 0). cbn [fst snd].
      split; [lia|].
      unfold cmp_inv.
      split; [reflexivity|]. split; [lia|]. split; [lia|].
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => exists (ms_regs msx), (ms_mem msx) end.
      eexists. split; [reflexivity|].
      split; [exact HJ|].
      split; [ca_kept KRg|]. split; [ca_kept KRg|]. split; [ca_kept KRg|]. split; [ca_kept KRg|].
      split; [ca_kept KRg|].
      split; [exact Q19|]. split; [exact Q26|].
      split; [ca_kept KRg|]. split; [ca_kept KRg|]. split; [ca_kept KRg|].
      split; [exact Q23|]. split; [exact Q18|]. split; [exact Q27|].
      split; [exact Q24|]. split; [exact Q25|].
      split; [exact KR|]. split; [exact GR|].
      ca_slots12 HRf Usp A33 A36 A35 A39 A32 A37 A34 A38 A43.
  + (* not taken: c + 1 = nch; +0x718 .. +0x72c the reloads, +0x730 `bnez s10` (s10 = 0: the engine takes the
       fall-through), +0x734: cmp_x734 *)
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x734; [ca_awr (d_sp1 cx) (d_sp0 cx) Usp |].
    ca_md. ca_kupd (d_sp1 cx) Usp KR GR.
    ca_final HS HAE KRg HRf ([2%bv; 3%bv; 4%bv; 8%bv; 9%bv] : list (bv 5)).
    ca_reg_at HS (19%bv : bv 5) (w64 (d_F cx)) Q19 ltac:(exact (cmp_den_atom E 35%nat _ A35)).
    ca_reg_at HS (21%bv : bv 5) (w64 (d_F cx)) Q21 ltac:(exact (cmp_den_atom E 35%nat _ A35)).
    ca_reg_at HS (27%bv : bv 5) (w64 (d_SH cx)) Q27 ltac:(exact (cmp_den_atom E 36%nat _ A36)).
    ca_reg_at HS (17%bv : bv 5) (w64 out) Q17 ltac:(exact (cmp_den_atom E 34%nat _ A34)).
    ca_reg_at HS (18%bv : bv 5) (w64 SHADOW_OFF) Q18 ltac:(exact (cmp_den_atom E 32%nat _ A32)).
    ca_reg_at HS (20%bv : bv 5) (w64 res) Q20 ltac:(exact (cmp_den_atom E 33%nat _ A33)).
    pmkst HS.
    apply SRr_ret. cbv beta. left.
    unfold cmp_x734.
    split; [reflexivity|].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => exists (ms_regs msx), (ms_mem msx) end.
    eexists. split; [reflexivity|].
    split; [exact HJ|].
    split; [ca_kept KRg|]. split; [ca_kept KRg|]. split; [ca_kept KRg|]. split; [ca_kept KRg|].
    split; [ca_kept KRg|].
    split; [exact (conj Q19 (conj Q21 Q27))|].
    split; [exact Q17|]. split; [exact Q18|]. split; [exact Q20|].
    split; [exact KR|]. split; [exact GR|].
    split; [ca_slota HRf Usp 8 33%nat A33|]. split; [ca_slota HRf Usp 16 36%nat A36|].
    split; [ca_slota HRf Usp 24 35%nat A35|]. split; [ca_slota HRf Usp 40 32%nat A32|].
    split; [ca_slota HRf Usp 48 35%nat A35|]. split; [ca_slota HRf Usp 56 37%nat A37|].
    split; [ca_slot64 HRf Usp A33|]. split; [ca_slota HRf Usp 72 34%nat A34|].
    ca_slota HRf Usp 112 35%nat A35.
Qed.

(* One turn of the bcmp double loop, from the inner head +0x6e0: cmp_l34_call (the call, up to its return
   +0x6f0), then cmp_l34_after. *)
Lemma cmp_l34_body : forall (cx : dctx) ly5 S5 (W5 : world decodesegs0) regs5 mem5 md5 res out mode nch ns,
  AR_laws decodesegs0 B ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc decodesegs0 B (decode_sigma DS___interceptor_trampoline_bcmp)) ->
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_a_core B cx ly5 S5 W5 regs5 mem5 md5 dec_ev_5fc ->
  Permutation (ablocks B ly5 S5) (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++
                                  [(out, dec_a_olen nch ns)]) ->
  4096 <= res -> 4096 <= out ->
  mo_le MT (d_S cx) S5 (dec_spent_5fc MT (d_n cx)) -> mo_ok MT S5 (dec_rest_5fc MT) ->
  CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
  dec_a_mode_ok cx W5 mem5 mode nch ns ->
  dec_a_fsh cx (aview decodesegs0 (w_H W5) mem5) 0 4 ->
  garr8 decodesegs0 (mrestrict (w_H W5) mem5) res (map (fun b : byte => bv_unsigned b) (d_body cx)) ->
  garr8 decodesegs0 (mrestrict (w_H W5) mem5) out
    (map (fun b : byte => bv_unsigned b) (CPlain.plain_out (d_body cx) nch ns)) ->
  frm_zero (@fp_csr fx) ->
  forall (x : Z * Z) (W : world decodesegs0) (c' : config),
    @cmp_inv rc B fx cx ly5 S5 W5 mem5 res out nch ns (fst x) (snd x) W c' ->
    SRr decodesegs0 W c' (fun W2 c2 => @cmp_x734 rc B fx cx ly5 S5 W5 mem5 res out W2 c2 \/
      exists x', 0 <= nch * ns - (fst x' * ns + snd x') < nch * ns - (fst x * ns + snd x) /\
                 @cmp_inv rc B fx cx ly5 S5 W5 mem5 res out nch ns (fst x') (snd x') W2 c2).
Proof.
intros cx ly5 S5 W5 regs5 mem5 md5 res out mode nch ns LAWS ABCMP HB Hcore5 Hperm5 Hres4096 Hout4096
  Hmle5 Hmok5 HP Hmode5 Hfsh5 Hres5 Hout5 Hfrm x W c' Hinv.
eapply SRr_bind.
- exact (@cmp_l34_call rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI fx
    cx ly5 S5 W5 regs5 mem5 md5 res out nch ns LAWS ABCMP HB Hcore5 Hperm5 HP Hres5 Hout5 (fst x) (snd x) W c' Hinv).
- intros W2 c2 _ H6.
  exact (cmp_l34_after cx ly5 S5 W5 regs5 mem5 md5 res out nch ns LAWS Hcore5 Hperm5 HP (fst x) (snd x) W2 c2 H6).
Qed.

End body2.
End x.
