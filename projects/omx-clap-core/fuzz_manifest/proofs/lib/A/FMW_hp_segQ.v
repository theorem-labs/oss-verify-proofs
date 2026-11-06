(* has_prefixed (G2) loop segment post: 0x82220..0x8223c and 0x8227c (lv2_locate.c:71, name_char (at[local_len])),
   kit lib/A/FMW_hp_kit.v. 0x82220 a0 = at + |lb|; 0x82224..0x82234 the inline check of at[|lb|] (shadow load,
   `bnez`, slow path 0x82264, report 0x822bc) and `lbu`; 0x82238 name_char (at[|lb|]); 0x8223c `beqz a0`: 0 ->
   0x8227c `li a0, 1` -> epilogue 0x82280 (hp_ret), else the loop tail 0x82240. The checked byte is the text's byte
   a + |lb| or its NUL (a + |lb| <= |tb| by has_prefixed_model.mt_len), so the token engine takes the check's
   fall-through: the report call 0x822bc is REFUTED. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YN3v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI16 YI00 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g2rt FMW_name_char FMW_hp_kit FMW_hp_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel has_prefixed_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the byte after the location, at[|lb|] *)
Local Abbreviation sgQ_byte cx a := (ManifestModel.byte_at (cx_tb cx) (Nat.add a (length (cx_lb cx)))).

(* a register read back as the engine's unsigned value of its symbolic content *)
Ltac sgQ_ureg HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    let Eg := fresh "Eg" in
    assert (Eg : sr_get (ss_regs ss) r = e) by (vm_compute; reflexivity);
    assert (Hr : getr (ms_regs ms) r = Z_to_bv 64 (U E e))
      by exact (eq_trans (st_ok_restrict_reg segs H E ss ms r HS) (eq_trans (f_equal (sv_denot E) Eg) (denot_lit_U E e)));
    clear Eg
  end.
(* a run over read-only regions changed no byte *)
Ltac sgQ_ro HF EM :=
  lazymatch type of HF with
  | frame_of ?E ?rs ?m ?m' => assert (EM : m' = m) by exact (frame_of_read_only E rs m m' eq_refl HF)
  end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis TL : TfibLib B.
Hypothesis IMGF : fm_img_facts tfibsegs B.
Hypothesis AISALNUM : aisalnum_realizes tfibsegs B PC_isalnum.

(* the loop state after a run that wrote nothing and kept s5 and the HP_KEEP registers *)
Lemma sgQ_move : forall cx a lyc Sc W regs m mdc E ss ms md' extra,
  hp_st B cx a lyc Sc W regs m mdc ->
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK_has_prefixed (spZ (cx_regs0 cx)) [] (cx_ly cx) (cx_S cx) (cx_W0 cx) (cx_mem cx) (cx_md cx)
    [] lyc Sc W (ms_mem ms) md' 0 ->
  ms_mem ms = m ->
  env_agree 32 (Ereg regs extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    ((21%bv : bv 5) :: HP_KEEP) = true ->
  hp_st B cx a lyc Sc W (ms_regs ms) (ms_mem ms) md'.
Proof.
intros cx a lyc Sc W regs m mdc E ss ms md' extra H HS HJ EM HAE Hcs.
pose proof (regs_keep_of_st_ok ((21%bv : bv 5) :: HP_KEEP) E ss (restrict (w_H W) ms) regs extra HS HAE Hcs) as HK.
cbn [restrict ms_regs] in HK.
apply (hp_st_move B cx a a lyc Sc W regs m mdc (ms_regs ms) (ms_mem ms) md' H HJ).
- rewrite EM. apply gframe_refl.
- intros r Hr. apply HK. right. exact Hr.
- pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q21 & _).
  rewrite <- Q21. apply HK. left. reflexivity.
- pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmt & _). exact Hmt.
Qed.

(* 0x8223c `beqz a0` on name_char's answer: 0 -> 0x8227c `li a0, 1` -> 0x82280, return 1; else the tail 0x82240 *)
Lemma sgQ_ret : forall cx a,
  (ManifestModel.name_char (sgQ_byte cx a) = false -> hp_res cx = 1) ->
  hp_cont B cx HP_TAIL a (fun _ => ManifestModel.name_char (sgQ_byte cx a) = true) ->
  forall lyc Sc W regs m mdc, hp_st B cx a lyc Sc W regs m mdc ->
  getr regs 10 = w64 (if ManifestModel.name_char (sgQ_byte cx a) then 1 else 0) ->
  SRr tfibsegs W (cfg_at tfibsegs 0x8223c regs m mdc) (hp_post B cx).
Proof.
intros cx a K1 KT lyc Sc W regs m mdc Hst H10.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof (hp_seat B cx a lyc Sc W regs m mdc 0x8223c Hst) as HS.
pose proof Hst as (_ & HJ & _).
assert (U10 : U (Ereg regs []) (SOff 10 0) = if ManifestModel.name_char (sgQ_byte cx a) then 1 else 0).
{ apply U_atom; [rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10
                | destruct (ManifestModel.name_char (sgQ_byte cx a)); lia]. }
unfold cfg_at. change (w64 0x8223c) with (Z_to_bv 64 0x8223c).
srr_branch_with tbl_hp_ok HS.
- (* a0 = 0: at[|lb|] is no name character, return 1 *)
  rewrite branch_eq_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc.
  assert (Enc : ManifestModel.name_char (sgQ_byte cx a) = false).
  { revert Hc. destruct (ManifestModel.name_char (sgQ_byte cx a)); intros Hc; [discriminate Hc | reflexivity]. }
  pose proof (K1 Enc) as Hres.
  aj_run_to tbl_hp_ok HS HJ 0x82280.
  { apply awr_ok_nil. }
  sgQ_ro HF EM. clear HF HFr HG.
  pose proof (sgQ_move cx a lyc Sc W regs m mdc _ _ ms _ [] Hst HS HJ EM (env_agree_refl 32 _)
    ltac:(vm_compute; reflexivity)) as Hst1.
  rreg HS (10%bv : bv 5) R10.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (hp_ret B TL cx a lyc Sc W (ms_regs ms) (ms_mem ms) _ Hst1).
  rewrite R10, Hres. reflexivity.
- (* a0 <> 0: at[|lb|] is a name character, on to the tail *)
  rewrite branch_eq_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
  assert (Enc : ManifestModel.name_char (sgQ_byte cx a) = true).
  { revert Hc. destruct (ManifestModel.name_char (sgQ_byte cx a)); intros Hc; [reflexivity | exfalso; exact (Hc eq_refl)]. }
  aj_run_to tbl_hp_ok HS HJ 0x82240.
  { apply awr_ok_nil. }
  sgQ_ro HF EM. clear HF HFr HG.
  pose proof (sgQ_move cx a lyc Sc W regs m mdc _ _ ms _ [] Hst HS HJ EM (env_agree_refl 32 _)
    ltac:(vm_compute; reflexivity)) as Hst1.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc].
  exact (KT _ _ _ _ _ _ Hst1 Enc).
Qed.

(* 0x82224..0x82238: the check of at[|lb|] (report 0x822bc refuted), `lbu`, the call name_char (at[|lb|]) *)
Lemma sgQ_chk : forall cx a,
  (ManifestModel.name_char (sgQ_byte cx a) = false -> hp_res cx = 1) ->
  hp_cont B cx HP_TAIL a (fun _ => ManifestModel.name_char (sgQ_byte cx a) = true) ->
  forall lyc Sc W regs m mdc, hp_st B cx a lyc Sc W regs m mdc ->
  getr regs 10 = w64 (cx_t cx + Z.of_nat (a + length (cx_lb cx))) ->
  SRr tfibsegs W (cfg_at tfibsegs 0x82224 regs m mdc) (hp_post B cx).
Proof.
intros cx a K1 KT lyc Sc W regs m mdc Hst H10.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx. ceil2.
pose proof Hst as (_ & HJ & _).
pose proof Hst as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmt & _).
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Hlen.
pose proof (hp_cstr B IMGF cx a lyc Sc W regs m mdc Hst) as (Ht & _).
pose proof Ht as (_ & Ht4096 & Htcl & _).
assert (Hi : (a + length (cx_lb cx) <= length (cx_tb cx))%nat) by lia.
assert (Hx : 4096 <= cx_t cx + Z.of_nat (a + length (cx_lb cx)) <= 2 ^ 47 - 8) by lia.
pose proof (hp_tbyte B IMGF cx a lyc Sc W regs m mdc _ Hst Hi) as (Hv & Hc).
pose proof (hp_seat_chk B cx a lyc Sc W regs m mdc 0x82224 _ _ Hst H10 Hx Hv Hc) as HS.
pose proof (hp_shok B IMGF cx a lyc Sc W regs m mdc (sgQ_byte cx a) _ Hst H10 Hi) as SHOK.
unfold cfg_at. change (w64 0x82224) with (Z_to_bv 64 0x82224).
(* the token engine discharges the check from the shadow entry of at[|lb|] and takes the fall-through: the report
   branch to 0x822bc is refuted; it stops at name_char's entry with ra = 0x8223c *)
aj_run_tok tbl_hp_ok HS HJ SHOK hp_Bspan.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
sgQ_ro HF EM. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?E2 _ _ =>
  assert (HAE : env_agree 32 (Ereg regs [w64 (sgQ_byte cx a)]) E2)
    by env_agree_chain (env_agree_refl 32 (Ereg regs [w64 (sgQ_byte cx a)])) end.
pose proof (sgQ_move cx a lyc Sc W regs m mdc _ _ ms _ _ Hst HS HJ EM HAE ltac:(vm_compute; reflexivity)) as Hst1.
rreg HS (1%bv : bv 5) R1.
sgQ_ureg HS (10%bv : bv 5) U10.
assert (R10 : getr (ms_regs ms) 10 = w64 (sgQ_byte cx a)).
{ rewrite U10, U_zext, (U_atom _ 32 (sgQ_byte cx a));
    [| cbn [ew ewset Nat.eqb]; exact (ew_Ereg_extra regs _ 0) | lia].
  change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc].
apply (hp_call_nc B IMGF AISALNUM cx a lyc Sc W (ms_regs ms) (ms_mem ms) _ 0x8223c (sgQ_byte cx a) Hst1 R1
  ltac:(lia) eq_refl R10 Hc).
intros ly2 S2 W2 regs2 m2 md2 Hst2 _ H10'.
exact (sgQ_ret cx a K1 KT ly2 S2 W2 regs2 m2 md2 Hst2 H10').
Qed.

(* 0x82220: a0 = at + |lb| *)
Lemma hp_seg_post : seg_post_ok B.
Proof.
unfold seg_post_ok, hp_cont. intros cx a K1 KT lyc Sc W regs m mdc Hst _.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx. ceil2.
pose proof Hst as (_ & HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q20 & Q21 & _ & _ & _ & _ & Hmt & _).
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Hlen.
pose proof (hp_cstr B IMGF cx a lyc Sc W regs m mdc Hst) as (Ht & _).
pose proof Ht as (_ & Ht4096 & Htcl & _).
assert (U21 : U (Ereg regs []) (SOff 21 0) = cx_t cx + Z.of_nat a).
{ apply U_atom; [rewrite (ew_Ereg_nat regs [] 21 21%bv eq_refl); exact Q21 | lia]. }
assert (U20 : U (Ereg regs []) (SOff 20 0) = Z.of_nat (length (cx_lb cx))).
{ apply U_atom; [rewrite (ew_Ereg_nat regs [] 20 20%bv eq_refl); exact Q20 | lia]. }
pose proof (hp_seat B cx a lyc Sc W regs m mdc 0x82220 Hst) as HS.
unfold cfg_at, HP_POST. change (w64 0x82220) with (Z_to_bv 64 0x82220).
aj_run_to tbl_hp_ok HS HJ 0x82224.
{ apply awr_ok_nil. }
sgQ_ro HF EM. clear HF HFr HG.
pose proof (sgQ_move cx a lyc Sc W regs m mdc _ _ ms _ [] Hst HS HJ EM (env_agree_refl 32 _)
  ltac:(vm_compute; reflexivity)) as Hst1.
sgQ_ureg HS (10%bv : bv 5) U10.
assert (R10 : getr (ms_regs ms) 10 = w64 (cx_t cx + Z.of_nat (a + length (cx_lb cx)))).
{ rewrite U10, U_add2, U21, U20. rewrite Z.mod_small by lia. unfold w64. f_equal. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc].
exact (sgQ_chk cx a K1 KT lyc Sc W (ms_regs ms) (ms_mem ms) _ Hst1 R10).
Qed.
End s.
