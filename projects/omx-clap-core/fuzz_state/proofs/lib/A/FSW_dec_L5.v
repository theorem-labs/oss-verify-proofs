(* preset_base64_decode (fs.asan 0x8481c), part L helper a Theorem Labs lane: the LAST loop iteration,
   at the text's NUL (i = length tb). The tail checks (bits <= 5, the unused low bits of acc, pad <= 2) are
   WriterSpec.six_tail_ok and b64_dec's `pad <=? 2`; they lead either to the call of fuzz_free (b64_dec tb = None) or to
   the store of n to *lenp and the return of q (dec_post's THIRD arm). Contract: (internal path).
   SCRATCH part (owner a Theorem Labs lane); a Theorem Labs lane integrates.
   MEASURED with the token engine over FSW_writer_tbl.fsw_wr_tbl (scratch FSW_dec_L5m.v in the VM workspace, removed):
   from decL_hss with the atom fact (47, [0, 0]) the run stops at 0x848dc (the whitespace test, symbolic), then at
   0x848ec (`c == 0`, symbolic), then - the NUL taken - at 0x84970 (`bge 5, s8`), which the engine decides from the
   atom fact of s8: bits = 6 reaches A_fuzz_free (a0 = SOff 9 0 = q, ra = SLit 0x8497c), bits <= 4 stops at 0x849d0
   (`acc & ~(-1 <<w bits) != 0`, symbolic) and then at DEC_EXIT_PAD = 0x849d8 (`blt 2, s10`, symbolic, a0 = SLit 2).
   From decL_lss with the atom fact (10, [2, 2]) the success tail runs to the final `ret` 0x849bc (= 543164), storing
   CVal 8 (SOff 22 0) = n in the region decL_lpr at atom 33 = lenp. From decL_lss_ff (the same state, with lenp's atom
   fact [4096, 2^47 - 8] for the fake-frame placement) the run ends at the same `ret` with the same registers and regions,
   no obligation left (scratch FSW_dec_L5q.v, a build machine, 2026-10-29T05:48Z). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_writer
FSW_K FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSW_dec_defs FSW_dec_L0 FSW_dec_L1 FSW_dec_L2 FSW_dec_L3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- a state with one more atom fact (YP06 st_ok_facts / facts_ok_add_atom) ---- *)
Definition decLN_addf (ss : sstate) (n : nat) (f : afact) : sstate :=
  mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss)
    (mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Section G. Context {fx : YK11.FPState}.
Lemma decLN_add_atom : forall E ss ms n f,
  st_ok tfibsegs E ss ms -> afact_ok E n f -> st_ok tfibsegs E (decLN_addf ss n f) ms.
Proof.
intros E ss ms n f HS Hf. unfold decLN_addf. apply (st_ok_facts tfibsegs E ss ms); [exact HS|].
apply facts_ok_add_atom; [exact (st_ok_facts_ok tfibsegs E ss ms HS) | exact Hf].
Qed.
End G.
(* an atom fact from the value of the atom (the two forms the file needs) *)
Lemma decLN_af : forall E n v lo hi, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  afact_ok E n (mkAF lo hi 0).
Proof.
intros E n v lo hi Hn Hv Hr. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hn, (wz v Hv).
split; [exact Hr|]. rewrite Z.pow_0_r, Z.mod_1_r. split; [reflexivity | lia].
Qed.
Lemma decLN_af1 : forall E n v lo hi, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 = 0 ->
  afact_ok E n (mkAF lo hi 1).
Proof.
intros E n v lo hi Hn Hv Hr Hm. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hn, (wz v Hv).
split; [exact Hr|]. change (2 ^ 1) with 2. split; [exact Hm | lia].
Qed.

(* ---- the memory outside the regions a run may write ---- *)
Lemma decLN_frame_out : forall E (rs : list YP09.region) (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs m m' ->
  (forall r a, In r rs ->
     base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros E rs m m' P HF HP a Ha HnP. apply HF. intros (r & Hin & Hr). rewrite (wz a Ha) in Hr.
exact (HnP (HP r a Hin Hr)).
Qed.

(* ---- the write windows of a run from a cut: the frame (its only stack region) and the regions rs ---- *)
Lemma decLN_awr_ro : forall B E rs STK sp0 FP bl0 blc ly own fr0,
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> awr_ok tfibsegs B E rs STK sp0 FP bl0 blc ly own fr0.
Proof.
intros B E rs. induction rs as [|r rs IH]; intros STK sp0 FP bl0 blc ly own fr0 HF; [apply awr_ok_nil|].
inversion HF as [|? ? Hr Hrs]; subst. apply awr_ok_cons_ro; [exact Hr | exact (IH _ _ _ _ _ _ _ _ Hrs)].
Qed.
Lemma decLN_awr0 : forall B E d rs bl0 blc ly fr0,
  bv_unsigned (ew E 2) = d_sp d - DEC_F -> d_sp d <= d_ot d ->
  awr_ok tfibsegs B E rs (d_STKJ d) (d_ot d) (d_FP d) bl0 blc ly [] fr0 ->
  awr_ok tfibsegs B E (fsT_ret_regions DEC_F decL_cs rs) (d_STKJ d) (d_ot d) (d_FP d) bl0 blc ly [] fr0.
Proof.
intros B E d rs bl0 blc ly fr0 E2 Hspot Hrs.
assert (HSTK : 112 <= STK_preset_base64_decode) by (vm_compute; discriminate).
unfold fsT_ret_regions.
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := d_sp d - DEC_F - d_ot d);
  [reflexivity | rewrite E2; lia
   | cbv [fstk_ret YP09.r_wlo]; unfold d_STKJ, DEC_F in *; lia
   | cbv [fstk_ret YP09.r_whi]; unfold DEC_F in *; lia |].
apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
exact Hrs.
Qed.

(* ---- the 13 saved entry values, read off the env of a cut ---- *)
Lemma decLN_E_sav : forall d regs ex (j : nat), (j < 13)%nat ->
  ew (decL_E d regs ex) (34 + j) = getr (d_regs d) (nth j dec_saved 0%bv).
Proof.
intros d regs ex j Hj. unfold decL_E. replace (34 + j)%nat with (32 + (2 + j))%nat by lia.
rewrite ew_Ereg_extra. unfold decL_xs, fs_extraT, dec_saved.
do 13 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

(* the success tail's state when *lenp lies in a caller fake frame: lenp anywhere in [4096, 2^47 - 8], 8-aligned *)
Definition decL_lgf_ff : list (nat * afact) := (33%nat, mkAF 4096 (2 ^ 47 - 8) 3) :: decL_sgf 0 2 0 6.
Definition decL_lss_ff : sstate := fss_retT DEC_EXIT_PAD DEC_F decL_cs [decL_lpr] decL_lgf_ff.

(* the shadow byte of an 8-aligned 8-byte object inside a 32-aligned frame lies in the frame's shadow range *)
Lemma decLN_sh_frame : forall f bs lo x, f mod 32 = 0 -> lo mod 8 = 0 -> f <= lo -> lo + 8 <= f + bs ->
  lo <= x < lo + 8 -> shadow_addr f <= shadow_of_addr SHADOW_OFF x < shadow_addr f + bs / 8.
Proof. intros f bs lo x H1 H2 H3 H4 H5. unfold shadow_addr, shadow_of_addr. Z.div_mod_to_equations. lia. Qed.
(* the shadow byte of an application address below 2^47 lies in the shadow band *)
Lemma decLN_sh_bounds : forall x, 0 <= x < 2 ^ 47 ->
  SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 17592186044416.
Proof.
intros x Hx. change (2 ^ 47) with 140737488355328 in Hx. unfold shadow_of_addr, SHADOW_OFF.
Z.div_mod_to_equations. lia.
Qed.
(* a shadow-band byte is in no FP range of the fake-frame placement *)
Lemma decLN_notFP : forall lo s, (s < lo \/ lo + 8 <= s) -> 0x5da608 <= s ->
  ~ inFP (FS_PSTAT_FP ++ [(lo, lo + 8)]) s.
Proof.
intros lo s H1 H2 (r & Hr & Ha). apply in_app_iff in Hr.
destruct Hr as [Hr | Hr];
  [unfold FS_PSTAT_FP in Hr; destruct Hr as [<-|[<-|[<-|[<-|[]]]]] | destruct Hr as [<-|[]]];
  cbn [fst snd] in Ha; lia.
Qed.

Section L5. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the two shadow-base cells of the image (FSH_Base.v:116), as every lane's entry / resume lemma asks them *)
Hypothesis HSS : FsShadowSyms B.

(* FSW_dec_L3.v (a Theorem Labs lane) landed rc=0 (a Theorem Labs lane, 02:0xZ), so its lemmas are IMPORTED, not copied: decLB_text, decLB_q,
   decLB_keep, decLB_memf, decLB_lenp, decLB_sp (each takes B CTX first, decLB_memf only B). *)
Let decLN_head_st := decL_head_st B HSS (decLB_text B) (decLB_q B).

(* ---- the cut re-assembled at the memory and registers the engine left ---- *)
Lemma decLN_rehead : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ex ss ms md',
  dec_entry_ok B d ->
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  st_ok tfibsegs Ex ss (restrict (w_H Wc) ms) ->
  nth_error (ss_mem ss) 0 = Some (fstk_ret DEC_F decL_cs) ->
  (forall n, (n < 47)%nat -> ew Ex n = ew (decL_E d regsc ex) n) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv = true ->
  dec_J B d lyc Sc Wc Uc (ms_mem ms) md' k -> ARU tfibsegs B lyc Sc Uc Wc (ms_mem ms) md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
     ms_mem ms (Z_to_bv 64 a) = memc (Z_to_bv 64 a)) ->
  dec_head B d q i six pad acc Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ex ss ms md' HE HH HS Hnth HEx HRb HJ2 HARU2 MEQ.
pose proof (decLB_sp B d HE) as (SP1 & SP2 & SP3).
pose proof (decL_lenp_range B d HE) as (L1 & L2 & _).
assert (HR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0).
{ intros r Hin. apply sv_eqb_eq. exact (proj1 (forallb_forall _ _) HRb r Hin). }
pose proof HH as HH0. decL_unhead HH.
(* the registers of the cut, read back *)
assert (RG : forall (r : bv 5) (n : nat), In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  Z.of_nat n = bv_unsigned r -> getr (ms_regs ms) r = getr regsc r).
{ intros r n Hin Hn.
  rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) Ex ss ms r HS), (HR r Hin).
  rewrite fsw_SOff0, (HEx (Z.to_nat (bv_unsigned r)) ltac:(pose proof (u5_range r); lia)).
  rewrite (decL_E_reg d regsc ex (Z.to_nat (bv_unsigned r)) r ltac:(pose proof (u5_range r); lia)).
  reflexivity. }
assert (E2 : bv_unsigned (ew Ex 2) = d_sp d - DEC_F)
  by (rewrite (HEx 2%nat ltac:(lia)), (decL_E_reg d regsc ex 2 2%bv eq_refl); exact Hsp).
destruct (decL_frame_back d regsc ex Wc ms Ex ss HS Hnth E2
  ltac:(intros n Hn; apply HEx; lia) ltac:(lia)) as (HFr' & HLs').
apply (decL_mk_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k i six pad acc (ms_regs ms) (ms_mem ms) md' HH0
  HJ2 HARU2);
  [ (* decL_memf at the new memory *)
    apply (decLB_keep B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc (ms_mem ms)
             (d_sp d - DEC_F) (d_sp d) HE HH0 (decLB_memf B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH0));
    [ unfold DEC_F; lia | lia
    | intros a Ha Hna; apply (aview_at tfibsegs); exact (MEQ a Ha Hna) ]
  | exact HFr' | exact HLs'
  | unfold spZ; rewrite (RG 2%bv 2%nat ltac:(cbv [In]; tauto) eq_refl); exact Hsp
  | rewrite (RG 3%bv 3%nat ltac:(cbv [In]; tauto) eq_refl); exact R3
  | rewrite (RG 4%bv 4%nat ltac:(cbv [In]; tauto) eq_refl); exact R4
  | rewrite (RG 8%bv 8%nat ltac:(cbv [In]; tauto) eq_refl); exact R8
  | rewrite (RG 9%bv 9%nat ltac:(cbv [In]; tauto) eq_refl); exact R9
  | rewrite (RG 18%bv 18%nat ltac:(cbv [In]; tauto) eq_refl); exact R18
  | rewrite (RG 19%bv 19%nat ltac:(cbv [In]; tauto) eq_refl); exact R19
  | rewrite (RG 20%bv 20%nat ltac:(cbv [In]; tauto) eq_refl); exact R20
  | rewrite (RG 21%bv 21%nat ltac:(cbv [In]; tauto) eq_refl); exact R21
  | rewrite (RG 22%bv 22%nat ltac:(cbv [In]; tauto) eq_refl); exact R22
  | rewrite (RG 23%bv 23%nat ltac:(cbv [In]; tauto) eq_refl); exact R23
  | exact Hacc
  | rewrite (RG 24%bv 24%nat ltac:(cbv [In]; tauto) eq_refl); exact R24
  | rewrite (RG 25%bv 25%nat ltac:(cbv [In]; tauto) eq_refl); exact R25
  | rewrite (RG 26%bv 26%nat ltac:(cbv [In]; tauto) eq_refl); exact R26
  | rewrite (RG 27%bv 27%nat ltac:(cbv [In]; tauto) eq_refl); exact R27
  | exact Hi | exact Hpad | exact Hsix | exact Hsix64 | exact Hlast | exact Hscan ].
Qed.

(* ---- a fail arm: the engine at the call of fuzz_free (a0 = q, ra = 0x8497c) ---- *)
Lemma decLN_free : forall d q i six pad acc Wc lyc Sc Uc md' k Ex ss ms,
  dec_head B d q i six pad acc Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  st_ok tfibsegs Ex ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = A_fuzz_free ->
  sr_get (ss_regs ss) 10 = SOff 9 0 -> sr_get (ss_regs ss) 1 = SLit DEC_RA_FREE ->
  ew Ex 9 = w64 q ->
  WriterSpec.b64_dec (d_tb d) = None ->
  SRr tfibsegs Wc (mkCfg ms md') (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc md' k Ex ss ms HH HFREE HS Hrv Hpc S10 S1 E9 Hdec.
pose proof HH as HH0. decL_unhead HH.
assert (R10 : getr (ms_regs ms) 10 = w64 q)
  by (exact (decL_reg (w_H Wc) Ex ss ms 10%bv _ _ HS S10 ltac:(rewrite fsw_SOff0; exact E9))).
assert (R1 : getr (ms_regs ms) 1 = w64 DEC_RA_FREE)
  by (exact (fsw_reg_lit (w_H Wc) Ex ss ms 1%bv DEC_RA_FREE HS S1 ltac:(unfold DEC_RA_FREE; lia))).
exact (decL_free B d q i six pad acc Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k Ex ss ms md' HH0 HFREE HS Hrv Hpc
  HJ HARU (decLB_memf B d q i six pad acc Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k HH0) HFr HLs R10 R1 Hsp R3 R4 R8
  Hdec).
Qed.

(* ---- the head at the NUL: the four tail tests; the fail arms close, the success arm reaches DEC_EXIT_PAD ---- *)
Lemma decLN_exit : forall d q six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d ->
  dec_head B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (forall regs' mem' md',
     dec_head B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regs' mem' md' k ->
     getr regs' 10 = w64 2 -> pad <= 2 -> WriterSpec.six_tail_ok six = true ->
     SRr tfibsegs Wc (mkCfg (YK11.mkst regs' (Z_to_bv 64 DEC_EXIT_PAD) mem' (YK11.seg_rom tfibsegs)) md')
       (dec_post B d)) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs)) mdc) (dec_post B d).
Proof.
intros d q six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE HCONT.
pose proof (decLB_sp B d HE) as (SP1 & SP2 & SP3).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & Htb & _).
assert (Hc0 : nth (length (d_tb d)) (d_tb d ++ [0]) 0 = 0)
  by (rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity).
destruct (decLN_head_st d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (HS & SHOK).
cbv zeta in HS, SHOK. rewrite Hc0 in HS, SHOK.
pose proof HH as HH0. decL_unhead HH. unfold dec_J in HJ.
set (E := decL_E d regsc [Z_to_bv 64 0]) in *.
assert (EE : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; unfold E; exact (decL_E_reg d regsc _ n r Hn)).
assert (E2 : bv_unsigned (ew E 2) = d_sp d - DEC_F)
  by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (E8 : ew E 8 = Z_to_bv 64 DEC_WSMASK) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E23 : ew E 23 = Z_to_bv 64 acc) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = Z_to_bv 64 (6 * Z.of_nat (length six) mod 8))
  by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E26 : ew E 26 = Z_to_bv 64 pad) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (E47 : ew E 47 = Z_to_bv 64 0) by (unfold E; exact (decL_E_ex d regsc _ 0)).
(* the model at the NUL *)
assert (HDEC : WriterSpec.b64_dec (d_tb d) = decLA_out pad six (skipn (length (d_tb d)) (d_tb d))) by exact Hscan.
rewrite decLA_skipn_end, decLA_out_nil in HDEC.
pose proof (decLA_tail six acc Hlast) as HTAIL.
assert (Hbits : 0 <= 6 * Z.of_nat (length six) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Hbits2 : (6 * Z.of_nat (length six) mod 8) mod 2 = 0) by (Z.div_mod_to_equations; lia).
assert (Hpad64 : 0 <= pad < 2 ^ 63) by lia.
(* ---- run 1: the head to the whitespace test 0x848dc ---- *)
pose proof (decLN_add_atom E decL_hss _ 47%nat (mkAF 0 0 0) HS
  (decLN_af E 47%nat 0 0 0 E47 ltac:(lia) ltac:(lia))) as HS1.
clear HS.
fsw_aj_run_tokU fsw_wr_tbl_ok HS1 HJ HARU SHOK fs_Bspan.
- cbv [decLN_addf decL_hss fss_retT ss_mem].
  apply (decLN_awr0 B E d [decL_txr] _ _ _ _ E2 ltac:(lia)).
  apply decLN_awr_ro. constructor; [cbv [decL_txr YP09.r_wlo YP09.r_whi]; lia | constructor].
- (* at 0x848dc *)
  set (E1 := ewset (ewset E 48 w) 49 w0) in *.
  assert (EX : forall n, (n < 48)%nat -> ew E1 n = ew E n)
    by (intros n Hn; unfold E1; rewrite !ew_ewset_other by lia; reflexivity).
  assert (X2 : bv_unsigned (ew E1 2) = d_sp d - DEC_F) by (rewrite (EX 2%nat ltac:(lia)); exact E2).
  assert (X8 : ew E1 8 = Z_to_bv 64 DEC_WSMASK) by (rewrite (EX 8%nat ltac:(lia)); exact E8).
  assert (X9 : ew E1 9 = Z_to_bv 64 q) by (rewrite (EX 9%nat ltac:(lia)); exact E9).
  assert (X23 : ew E1 23 = Z_to_bv 64 acc) by (rewrite (EX 23%nat ltac:(lia)); exact E23).
  assert (X24 : ew E1 24 = Z_to_bv 64 (6 * Z.of_nat (length six) mod 8))
    by (rewrite (EX 24%nat ltac:(lia)); exact E24).
  assert (X26 : ew E1 26 = Z_to_bv 64 pad) by (rewrite (EX 26%nat ltac:(lia)); exact E26).
  assert (X47 : ew E1 47 = Z_to_bv 64 0) by (rewrite (EX 47%nat ltac:(lia)); exact E47).
  assert (XE : forall n, (n < 47)%nat -> ew E1 n = ew (decL_E d regsc [Z_to_bv 64 0]) n)
    by (intros n Hn; rewrite (EX n ltac:(lia)); reflexivity).
  assert (MEQ1 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
    ms_mem ms (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
  { apply (decLN_frame_out E _ memc (ms_mem ms) (fun a => d_sp d - DEC_F <= a < d_sp d) HF).
    intros r a Hin Hr.
    cbv [decLN_addf decL_hss fss_retT ss_mem fsT_ret_regions app In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbv [fstk_ret fs_got_region fs_bcell_region decL_txr
           YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      try rewrite E2 in Hr; unfold DEC_F in *; lia. }
  clear HF HG.
  eapply (SRr_sym_branch tfibsegs Wc E1 _ ms _ _ BC_NE
            (SAlu ALU_AND (SAlu ALU_SRL (SOff 8 0) (SOff 47 0)) (SLit 1)) (SLit 0));
    [exact HS1 | intros Hb HS2 | intros Hb HS2].
  + (* whitespace: the NUL is not whitespace *)
    rewrite (decLA_br_ws E1 8 47 0 X8 X47 ltac:(lia)) in Hb. vm_compute in Hb. discriminate Hb.
  + (* not whitespace: run 2 to the `c == 0` test 0x848ec *)
    fsw_aj_run_tokU fsw_wr_tbl_ok HS2 HJ HARU SHOK fs_Bspan.
    * apply (decLN_awr0 B E1 d [decL_txr] _ _ _ _ X2 ltac:(lia)).
      apply decLN_awr_ro. constructor; [cbv [decL_txr YP09.r_wlo YP09.r_whi]; lia | constructor].
    * assert (FR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
        ms_mem ms0 (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
      { apply (decLN_frame_out E1 _ (ms_mem ms) (ms_mem ms0) (fun x => d_sp d - DEC_F <= x < d_sp d) HF).
        intros r a Hin Hr. cbn [ss_mem add_cond In] in Hin.
        destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          try rewrite X2 in Hr; unfold DEC_F in *; lia. }
      assert (MEQ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
        ms_mem ms0 (Z_to_bv 64 a) = memc (Z_to_bv 64 a))
        by (intros a Ha Hna; rewrite (FR2 a Ha Hna); exact (MEQ1 a Ha Hna)).
      clear HF HG FR2.
      eapply (SRr_sym_branch tfibsegs Wc E1 _ ms0 _ _ BC_EQ (SOff 47 0) (SLit 0));
        [exact HS2 | intros Hb2 HS3 | intros Hb2 HS3].
      -- (* the NUL: the loop exits. bits = 6 refuses at once, bits <= 4 goes on to the acc test *)
         assert (HB : 6 * Z.of_nat (length six) mod 8 <= 4 \/ 6 * Z.of_nat (length six) mod 8 = 6)
           by (pose proof (decLA_bits_cases (Z.of_nat (length six)) ltac:(lia)); lia).
         destruct HB as [HB|HB].
         ++ (* bits <= 4: run 3 to the `acc & ~(-1 <<w bits) != 0` test 0x849d0 *)
            pose proof (decLN_add_atom E1 _ _ 24%nat (mkAF 0 4 1) HS3
              (decLN_af1 E1 24%nat (6 * Z.of_nat (length six) mod 8) 0 4 X24 ltac:(lia) ltac:(lia) Hbits2)) as HS4.
            fsw_aj_run_tokU fsw_wr_tbl_ok HS4 HJ HARU SHOK fs_Bspan.
            ** apply (decLN_awr0 B E1 d [decL_txr] _ _ _ _ X2 ltac:(lia)).
               apply decLN_awr_ro. constructor; [cbv [decL_txr YP09.r_wlo YP09.r_whi]; lia | constructor].
            ** assert (FR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
                 ms_mem ms1 (Z_to_bv 64 a) = ms_mem ms0 (Z_to_bv 64 a)).
               { apply (decLN_frame_out E1 _ (ms_mem ms0) (ms_mem ms1)
                          (fun x => d_sp d - DEC_F <= x < d_sp d) HF).
                 intros r a Hin Hr. cbn [ss_mem add_cond decLN_addf In] in Hin.
                 destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
                   cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
                   try rewrite X2 in Hr; unfold DEC_F in *; lia. }
               assert (MEQ3 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
                 ms_mem ms1 (Z_to_bv 64 a) = memc (Z_to_bv 64 a))
                 by (intros a Ha Hna; rewrite (FR3 a Ha Hna); exact (MEQ2 a Ha Hna)).
               clear HF HG FR3.
               eapply (SRr_sym_branch tfibsegs Wc E1 _ ms1 _ _ BC_NE
                 (SAlu ALU_AND (SOff 23 0)
                    (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff 24 0)) (SLit (-1))))
                 (SLit 0));
                 [exact HS4 | intros Hb3 HS5 | intros Hb3 HS5].
               --- (* the unused low bits of acc are not 0: the tail refuses *)
                   rewrite (decLA_br_exit_and E1 23 24 acc (6 * Z.of_nat (length six) mod 8)
                              X23 Hacc X24 ltac:(lia)) in Hb3.
                   assert (HNONE : WriterSpec.b64_dec (d_tb d) = None).
                   { rewrite HDEC, HTAIL.
                     replace (acc mod 2 ^ (6 * Z.of_nat (length six) mod 8) =? 0) with false
                       by (symmetry; apply negb_true_iff in Hb3; exact Hb3).
                     rewrite andb_false_r, andb_false_r. reflexivity. }
                   fsw_aj_run_tokU fsw_wr_tbl_ok HS5 HJ HARU SHOK fs_Bspan.
                   +++ apply (decLN_awr0 B E1 d [decL_txr] _ _ _ _ X2 ltac:(lia)).
                       apply decLN_awr_ro.
                       constructor; [cbv [decL_txr YP09.r_wlo YP09.r_whi]; lia | constructor].
                   +++ assert (FR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
                         ms_mem ms2 (Z_to_bv 64 a) = ms_mem ms1 (Z_to_bv 64 a)).
                       { apply (decLN_frame_out E1 _ (ms_mem ms1) (ms_mem ms2)
                                  (fun x => d_sp d - DEC_F <= x < d_sp d) HF).
                         intros r a Hin Hr. cbn [ss_mem add_cond decLN_addf In] in Hin.
                         destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
                           cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
                           try rewrite X2 in Hr; unfold DEC_F in *; lia. }
                       assert (MEQ4 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
                         ms_mem ms2 (Z_to_bv 64 a) = memc (Z_to_bv 64 a))
                         by (intros a Ha Hna; rewrite (FR4 a Ha Hna); exact (MEQ3 a Ha Hna)).
                       eapply (decLN_free d q (length (d_tb d)) six pad acc Wc lyc Sc Uc _ k E1 _ ms2);
                         [ apply (decLN_rehead d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k
                                    E1 [Z_to_bv 64 0] _ ms2 _ HE HH0 HS5 ltac:(vm_compute; reflexivity) XE
                                    ltac:(vm_compute; reflexivity) HJ HARU MEQ4)
                         | exact HFREE | exact HS5 | vm_compute; reflexivity | vm_compute; reflexivity
                         | vm_compute; reflexivity | vm_compute; reflexivity | exact X9 | exact HNONE ].
               --- (* the low bits are 0: run 4 to DEC_EXIT_PAD *)
                   rewrite (decLA_br_exit_and E1 23 24 acc (6 * Z.of_nat (length six) mod 8)
                              X23 Hacc X24 ltac:(lia)) in Hb3.
                   assert (HTOK : WriterSpec.six_tail_ok six = true).
                   { rewrite HTAIL. apply negb_false_iff in Hb3. rewrite Hb3, andb_true_r.
                     apply Z.leb_le. lia. }
                   fsw_aj_run_tokU fsw_wr_tbl_ok HS5 HJ HARU SHOK fs_Bspan.
                   +++ apply (decLN_awr0 B E1 d [decL_txr] _ _ _ _ X2 ltac:(lia)).
                       apply decLN_awr_ro.
                       constructor; [cbv [decL_txr YP09.r_wlo YP09.r_whi]; lia | constructor].
                   +++ assert (FR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
                         ms_mem ms2 (Z_to_bv 64 a) = ms_mem ms1 (Z_to_bv 64 a)).
                       { apply (decLN_frame_out E1 _ (ms_mem ms1) (ms_mem ms2)
                                  (fun x => d_sp d - DEC_F <= x < d_sp d) HF).
                         intros r a Hin Hr. cbn [ss_mem add_cond decLN_addf In] in Hin.
                         destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
                           cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
                           try rewrite X2 in Hr; unfold DEC_F in *; lia. }
                       assert (MEQ4 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
                         ms_mem ms2 (Z_to_bv 64 a) = memc (Z_to_bv 64 a))
                         by (intros a Ha Hna; rewrite (FR4 a Ha Hna); exact (MEQ3 a Ha Hna)).
                       clear HF HG FR4.
                       eapply (SRr_sym_branch tfibsegs Wc E1 _ ms2 _ _ BC_LT (SLit 2) (SOff 26 0));
                         [exact HS5 | intros Hb4 HS6 | intros Hb4 HS6].
                       *** (* 2 < pad: the tail refuses *)
                           rewrite (decLA_br_lt_lit E1 26 pad 2 X26 ltac:(lia) ltac:(lia)) in Hb4.
                           apply Z.ltb_lt in Hb4.
                           assert (HNONE : WriterSpec.b64_dec (d_tb d) = None).
                           { rewrite HDEC. replace (pad <=? 2) with false
                               by (symmetry; apply Z.leb_gt; lia).
                             reflexivity. }
                           fsw_aj_run_tokU fsw_wr_tbl_ok HS6 HJ HARU SHOK fs_Bspan.
                           ---- apply (decLN_awr0 B E1 d [decL_txr] _ _ _ _ X2 ltac:(lia)).
                                apply decLN_awr_ro.
                                constructor; [cbv [decL_txr YP09.r_wlo YP09.r_whi]; lia | constructor].
                           ---- assert (FR5 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
                                  ms_mem ms3 (Z_to_bv 64 a) = ms_mem ms2 (Z_to_bv 64 a)).
                                { apply (decLN_frame_out E1 _ (ms_mem ms2) (ms_mem ms3)
                                           (fun x => d_sp d - DEC_F <= x < d_sp d) HF).
                                  intros r a Hin Hr. cbn [ss_mem add_cond decLN_addf In] in Hin.
                                  destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
                                    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
                                    try rewrite X2 in Hr; unfold DEC_F in *; lia. }
                                assert (MEQ5 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
                                  ms_mem ms3 (Z_to_bv 64 a) = memc (Z_to_bv 64 a))
                                  by (intros a Ha Hna; rewrite (FR5 a Ha Hna); exact (MEQ4 a Ha Hna)).
                                eapply (decLN_free d q (length (d_tb d)) six pad acc Wc lyc Sc Uc _ k E1 _ ms3);
                                  [ apply (decLN_rehead d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc
                                             mdc k E1 [Z_to_bv 64 0] _ ms3 _ HE HH0 HS6
                                             ltac:(vm_compute; reflexivity) XE
                                             ltac:(vm_compute; reflexivity) HJ HARU MEQ5)
                                  | exact HFREE | exact HS6 | vm_compute; reflexivity | vm_compute; reflexivity
                                  | vm_compute; reflexivity | vm_compute; reflexivity | exact X9 | exact HNONE ].
                       *** (* pad <= 2: the success tail, at DEC_EXIT_PAD with a0 = 2 *)
                           rewrite (decLA_br_lt_lit E1 26 pad 2 X26 ltac:(lia) ltac:(lia)) in Hb4.
                           apply Z.ltb_ge in Hb4.
                           rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) E1 _ ms2 HS6
                                      ltac:(vm_compute; reflexivity)).
                           apply (HCONT (ms_regs ms2) (ms_mem ms2) _);
                             [ apply (decLN_rehead d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k
                                        E1 [Z_to_bv 64 0] _ ms2 _ HE HH0 HS6 ltac:(vm_compute; reflexivity) XE
                                        ltac:(vm_compute; reflexivity) HJ HARU MEQ4)
                             | exact (fsw_reg_lit (w_H Wc) E1 _ ms2 10%bv 2 HS6 ltac:(vm_compute; reflexivity)
                                        ltac:(lia))
                             | exact Hb4 | exact HTOK ].
         ++ (* bits = 6: the tail refuses at 0x84970 *)
            pose proof (decLN_add_atom E1 _ _ 24%nat (mkAF 6 6 1) HS3
              (decLN_af1 E1 24%nat (6 * Z.of_nat (length six) mod 8) 6 6 X24 ltac:(lia) ltac:(lia) Hbits2)) as HS4.
            assert (HNONE : WriterSpec.b64_dec (d_tb d) = None).
            { rewrite HDEC, HTAIL, HB. replace (6 <=? 5) with false by reflexivity.
              rewrite andb_false_l, andb_false_r. reflexivity. }
            fsw_aj_run_tokU fsw_wr_tbl_ok HS4 HJ HARU SHOK fs_Bspan.
            ** apply (decLN_awr0 B E1 d [decL_txr] _ _ _ _ X2 ltac:(lia)).
               apply decLN_awr_ro. constructor; [cbv [decL_txr YP09.r_wlo YP09.r_whi]; lia | constructor].
            ** assert (FR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
                 ms_mem ms1 (Z_to_bv 64 a) = ms_mem ms0 (Z_to_bv 64 a)).
               { apply (decLN_frame_out E1 _ (ms_mem ms0) (ms_mem ms1)
                          (fun x => d_sp d - DEC_F <= x < d_sp d) HF).
                 intros r a Hin Hr. cbn [ss_mem add_cond decLN_addf In] in Hin.
                 destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
                   cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
                   try rewrite X2 in Hr; unfold DEC_F in *; lia. }
               assert (MEQ3 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
                 ms_mem ms1 (Z_to_bv 64 a) = memc (Z_to_bv 64 a))
                 by (intros a Ha Hna; rewrite (FR3 a Ha Hna); exact (MEQ2 a Ha Hna)).
               eapply (decLN_free d q (length (d_tb d)) six pad acc Wc lyc Sc Uc _ k E1 _ ms1);
                 [ apply (decLN_rehead d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k E1
                            [Z_to_bv 64 0] _ ms1 _ HE HH0 HS4 ltac:(vm_compute; reflexivity) XE
                            ltac:(vm_compute; reflexivity) HJ HARU MEQ3)
                 | exact HFREE | exact HS4 | vm_compute; reflexivity | vm_compute; reflexivity
                 | vm_compute; reflexivity | vm_compute; reflexivity | exact X9 | exact HNONE ].
      -- (* c <> 0 is impossible at the NUL *)
         rewrite (decLA_br_eq0 E1 47 0 X47 ltac:(lia)) in Hb2. cbn in Hb2. discriminate Hb2.
Qed.

(* ---- the atom facts of the s-registers at the NUL cut (pad <= 2, bits <= 6): L1's decL_head_st proof, with the
   narrower pad interval the tail tests give ---- *)
Lemma decLN_atoms : forall d q six pad acc Wc lyc Sc Uc regsc memc mdc k ex,
  dec_entry_ok B d ->
  dec_head B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  0 <= pad <= 2 ->
  atoms_ok (decL_E d regsc ex) (decL_sgf 0 2 0 6).
Proof.
intros d q six pad acc Wc lyc Sc Uc regsc memc mdc k ex HE HH Hpad2.
pose proof asan_consts as (C1 & _ & _ & _).
pose proof (decLB_q B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (Q16 & Q1 & Q2 & _).
pose proof (decLB_text B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (T1 & T2 & _).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & Htb & _).
pose proof (WriterSpecFacts.six_bytes_length six) as Hnb.
pose proof HH as HH0. decL_unhead HH.
assert (Hbits : 0 <= 6 * Z.of_nat (length six) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Hbits2 : (6 * Z.of_nat (length six) mod 8) mod 2 = 0) by (Z.div_mod_to_equations; lia).
assert (Hnb2 : 6 * Z.of_nat (length six) / 8 <= 2 ^ 30) by (Z.div_mod_to_equations; lia).
set (E := decL_E d regsc ex) in *.
unfold decL_sgf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
unfold E; rewrite (decL_E_reg d regsc ex 8 8%bv eq_refl). rewrite (decL_E_reg d regsc ex 9 9%bv eq_refl).
rewrite (decL_E_reg d regsc ex 18 18%bv eq_refl). rewrite (decL_E_reg d regsc ex 19 19%bv eq_refl).
rewrite (decL_E_reg d regsc ex 20 20%bv eq_refl). rewrite (decL_E_reg d regsc ex 21 21%bv eq_refl).
rewrite (decL_E_reg d regsc ex 22 22%bv eq_refl). rewrite (decL_E_reg d regsc ex 23 23%bv eq_refl).
rewrite (decL_E_reg d regsc ex 24 24%bv eq_refl). rewrite (decL_E_reg d regsc ex 25 25%bv eq_refl).
rewrite (decL_E_reg d regsc ex 26 26%bv eq_refl). rewrite (decL_E_reg d regsc ex 27 27%bv eq_refl).
rewrite R8, R9, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27.
pose proof Hrb as (_ & _ & Hn0 & _).
rewrite (decL_w64u DEC_WSMASK) by (unfold DEC_WSMASK; lia).
rewrite (decL_w64u q) by (unfold HEAD in *; lia).
rewrite (decL_w64u (d_text d + Z.of_nat (length (d_tb d)))) by lia.
rewrite (decL_w64u G_B64) by (unfold G_B64; lia).
rewrite (decL_w64u SHADOW_OFF) by (unfold SHADOW_OFF; lia).
rewrite (decL_w64u (Z.of_nat (length (WriterSpec.six_bytes six)))) by lia.
rewrite (decL_w64u acc) by lia.
rewrite (decL_w64u (6 * Z.of_nat (length six) mod 8)) by lia.
rewrite (decL_w64u 61) by lia. rewrite (decL_w64u pad) by lia. rewrite (decL_w64u 2) by lia.
rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold DEC_WSMASK, G_B64, DEC_CEIL, HEAD in *.
repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.

(* ---- the success arm, decode_spec's placement: lenp on the caller's real stack ---- *)
Lemma decLN_succ_rs : forall d q six pad acc Wc lyc Sc Uc regs2 mem2 md2 k,
  dec_entry_ok B d ->
  dec_head B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regs2 mem2 md2 k ->
  getr regs2 10 = w64 2 -> pad <= 2 -> WriterSpec.six_tail_ok six = true ->
  d_FP d = FS_PSTAT_FP ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regs2 (Z_to_bv 64 DEC_EXIT_PAD) mem2 (YK11.seg_rom tfibsegs)) md2)
    (dec_post B d).
Proof.
intros d q six pad acc Wc lyc Sc Uc regs2 mem2 md2 k HE HH R10 Hpad2 HTOK HFP.
pose proof asan_consts as (C1 & _ & _ & _).
pose proof (decLB_sp B d HE) as (SP1 & SP2 & SP3).
pose proof (decLB_q B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regs2 mem2 md2 k HE HH)
  as (Q16 & Q1 & Q2 & Qn & _).
pose proof (decLB_lenp B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regs2 mem2 md2 k HE HH HFP)
  as (LP1 & LP2 & LP3 & LP4 & LP5 & LP6 & LRA & LW).
pose proof (decLN_atoms d q six pad acc Wc lyc Sc Uc regs2 mem2 md2 k [] HE HH ltac:(pose proof HH as HH1;
  decL_unhead HH1; lia)) as HGF.
pose proof HH as HH0. decL_unhead HH. unfold dec_J in HJ.
pose proof HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & Htb & _).
pose proof (proj1 HPRE) as ((_ & HRET & _) & _).
pose proof HKe as (Kv & Kw & Kc & Kr).
pose proof Hglob as (_ & _ & _ & _ & GL1 & GL2 & GL3 & GL4).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcnt & _).
set (E := decL_E d regs2 []) in *.
assert (E2 : bv_unsigned (ew E 2) = d_sp d - DEC_F)
  by (unfold E; rewrite (decL_E_reg d regs2 [] 2 2%bv eq_refl); exact Hsp).
assert (E9 : ew E 9 = Z_to_bv 64 q)
  by (unfold E; rewrite (decL_E_reg d regs2 [] 9 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E; rewrite (decL_E_reg d regs2 [] 21 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = Z_to_bv 64 (Z.of_nat (length (WriterSpec.six_bytes six))))
  by (unfold E; rewrite (decL_E_reg d regs2 [] 22 22%bv eq_refl); exact R22).
assert (E33 : ew E 33 = Z_to_bv 64 (d_lenp d)) by (unfold E; exact (decL_E_lenp d regs2 [])).
assert (E33u : bv_unsigned (ew E 33) = d_lenp d) by (rewrite E33; apply wz; lia).
pose proof (WriterSpecFacts.six_bytes_length six) as Hnb.
assert (Hn64 : 0 <= Z.of_nat (length (WriterSpec.six_bytes six)) < 2 ^ 64) by lia.
(* the symbolic state of the success tail and its shadow entry for *lenp *)
assert (HS : st_ok tfibsegs E (decLN_addf decL_lss 10 (mkAF 2 2 0))
  (restrict (w_H Wc) (YK11.mkst regs2 (Z_to_bv 64 DEC_EXIT_PAD) mem2 (YK11.seg_rom tfibsegs)))).
{ apply decLN_add_atom;
    [| apply (decLN_af E 10%nat 2 2 2); [unfold E; rewrite (decL_E_reg d regs2 [] 10 10%bv eq_refl); exact R10
       | lia | lia]].
  unfold decL_lss.
  apply (decL_build B HSS d Wc lyc Sc Uc regs2 mem2 md2 k [] DEC_EXIT_PAD [decL_lpr] decL_lgf HE HJ HARU
    Hsp HFr HLs).
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold decL_lpr, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite E33u. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply LW. lia.
  - fold E. apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, decL_lpr, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E33u.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, DEC_F in *.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  - unfold decL_lgf. cbn [atoms_ok]. split; [|exact HGF].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite E33u.
    change (2 ^ 3) with 8. split; [lia | split; [exact LP3 | lia]]. }
assert (SHOK : sh_ok tfibsegs decL_Bx decL_lSH E (mrestrict (w_H Wc) mem2)).
{ unfold sh_ok, decL_lSH. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H Wc) mem2 E decL_Bx 33%nat (d_lenp d) 8 (d_lenp d) 0 8 LRA).
  - unfold decL_Bx. apply (U_atom E 21 SHADOW_OFF); [exact E21 | unfold SHADOW_OFF; lia].
  - apply (U_atom E 33 (d_lenp d)); [exact E33 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn in Hx. unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *. lia. }
(* the run to the final `ret` 0x849bc *)
fsw_aj_run_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan.
- cbv [decLN_addf decL_lss fss_retT ss_mem].
  apply (decLN_awr0 B E d [decL_lpr] _ _ _ _ E2 ltac:(lia)).
  eapply awr_ok_cons_gen with (k := 33%nat) (b := d_lenp d);
    [ reflexivity | exact E33u
    | cbv [decL_lpr YP09.r_wlo YP09.r_whi]; intros a Ha; left; left; unfold d_STKJ;
      assert (HSTK0 : 0 <= STK_preset_base64_decode) by (vm_compute; discriminate); lia
    | apply awr_ok_nil ].
- (* at the final `ret` 0x849bc: only the frame and *lenp were written *)
  subst k. subst Uc.
  assert (FR : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((d_sp d - DEC_F <= a < d_sp d) \/ (d_lenp d <= a < d_lenp d + 8)) ->
    ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
  { apply (decLN_frame_out E _ mem2 (ms_mem ms)
             (fun x => (d_sp d - DEC_F <= x < d_sp d) \/ (d_lenp d <= x < d_lenp d + 8)) HF).
    intros r a Hin Hr.
    cbv [decLN_addf decL_lss fss_retT ss_mem fsT_ret_regions app In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbv [fstk_ret fs_got_region fs_bcell_region decL_lpr
           YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      [ rewrite E2 in Hr; left; unfold DEC_F in *; lia | lia | lia | rewrite E33u in Hr; right; lia ]. }
  assert (SB : same_below mem2 (ms_mem ms) alloc_ceiling)
    by (intros x Hx; apply FR; [lia | unfold DEC_F in *; lia]).
  assert (E46 : ew E 46 = getr (d_regs d) 1%bv)
    by (unfold E; change 46%nat with (34 + 12)%nat; rewrite (decLN_E_sav d regs2 [] 12%nat ltac:(lia));
        reflexivity).
  assert (E2w : ew E 2 = w64 (d_sp d - DEC_F))
    by (unfold w64; rewrite <- E2; symmetry; apply Z_to_bv_bv_unsigned).
  assert (R1F : getr (ms_regs ms) 1 = getr (d_regs d) 1)
    by (exact (decL_reg (w_H Wc) E _ ms 1%bv (SOff 46 0) _ HS ltac:(vm_compute; reflexivity)
                 ltac:(rewrite fsw_SOff0; exact E46))).
  assert (R10F : getr (ms_regs ms) 10 = w64 q)
    by (exact (decL_reg (w_H Wc) E _ ms 10%bv (SOff 9 0) _ HS ltac:(vm_compute; reflexivity)
                 ltac:(rewrite fsw_SOff0; exact E9))).
  (* the callee-saved registers: sp back up by the frame, s0..s11 and ra reloaded from the frame words *)
  assert (HPRES : aregs_preserved (d_regs d) (ms_regs ms)).
  { lazymatch type of HS with
    | st_ok _ _ ?ssf _ =>
      apply (fsw_preserved (w_H Wc) E ssf ms (d_regs d) (fun r : bv 5 => sr_get (ss_regs ssf) r) HS);
      [vm_compute; reflexivity|];
      let r := fresh "r" in let Hr := fresh "Hr" in
      intros r Hr; cbv [CALLEE_SAVED In] in Hr;
      repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]
    end; cbv beta;
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
    - rewrite (decL_soff E 2 112 (d_sp d - DEC_F) E2w ltac:(unfold DEC_F in *; lia) ltac:(unfold DEC_F in *; lia)).
      replace (d_sp d - DEC_F + 112) with (d_sp d) by (unfold DEC_F; lia).
      unfold w64, d_sp, spZ. apply Z_to_bv_bv_unsigned.
    - rewrite fsw_SOff0. unfold E. rewrite (decL_E_reg d regs2 [] 3 3%bv eq_refl). exact R3.
    - rewrite fsw_SOff0. unfold E. rewrite (decL_E_reg d regs2 [] 4 4%bv eq_refl). exact R4.
    - rewrite fsw_SOff0. unfold E. change 45%nat with (34 + 11)%nat.
      rewrite (decLN_E_sav d regs2 [] 11%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 44%nat with (34 + 10)%nat.
      rewrite (decLN_E_sav d regs2 [] 10%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 43%nat with (34 + 9)%nat.
      rewrite (decLN_E_sav d regs2 [] 9%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 42%nat with (34 + 8)%nat.
      rewrite (decLN_E_sav d regs2 [] 8%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 41%nat with (34 + 7)%nat.
      rewrite (decLN_E_sav d regs2 [] 7%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 40%nat with (34 + 6)%nat.
      rewrite (decLN_E_sav d regs2 [] 6%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 39%nat with (34 + 5)%nat.
      rewrite (decLN_E_sav d regs2 [] 5%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 38%nat with (34 + 4)%nat.
      rewrite (decLN_E_sav d regs2 [] 4%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 37%nat with (34 + 3)%nat.
      rewrite (decLN_E_sav d regs2 [] 3%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 36%nat with (34 + 2)%nat.
      rewrite (decLN_E_sav d regs2 [] 2%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 35%nat with (34 + 1)%nat.
      rewrite (decLN_E_sav d regs2 [] 1%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 34%nat with (34 + 0)%nat.
      rewrite (decLN_E_sav d regs2 [] 0%nat ltac:(lia)). reflexivity. }
  (* the stored length, read back from the region of *lenp *)
  assert (VL : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) (d_lenp d) 8
                 (Z.of_nat (length (WriterSpec.six_bytes six)))).
  { lazymatch type of HS with
    | st_ok _ _ ?ssf _ =>
      pose proof (fsw_region_nth E ssf (restrict (w_H Wc) ms) 3%nat
        (YP09.mkRegion (Some 33%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 22 0))]) HS
        ltac:(vm_compute; reflexivity)) as HR3
    end.
    cbn [ms_mem restrict] in HR3.
    rewrite <- (Z.add_0_r (d_lenp d)).
    apply (fsw_field E _ 33%nat (d_lenp d) [YP09.mkChunk 0 (CVal 8 (SOff 22 0))] 0 8 0 8 0 8%N (SOff 22 0) _ HR3
             E33u);
      [ cbv [In]; tauto | rewrite fsw_SOff0; exact E22 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia ]. }
  assert (HSOME : WriterSpec.b64_dec (d_tb d) = Some (WriterSpec.six_bytes six)).
  { assert (HDEC : WriterSpec.b64_dec (d_tb d) = decLA_out pad six (skipn (length (d_tb d)) (d_tb d)))
      by exact Hscan.
    rewrite decLA_skipn_end, decLA_out_nil in HDEC.
    rewrite HDEC, HTOK. replace (pad <=? 2) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg _ ?mdX) _ =>
    assert (MAIN : SRr tfibsegs Wc (mkCfg ms mdX)
      (fpostU tfibsegs B (d_STKJ d) (d_ot d) (d_FP d) (d_regs d) (d_ly d) (d_S d) (d_U d) (d_W d) (d_mem d)
         (d_md d) 1 (d_U d ++ [(q - HEAD, HEAD)])
         (fun (ly' : alayout) (S' : astate) (W' : world tfibsegs) (regs' : bvmap 5 word)
              (mem' : word -> option byte) (md' : Model) =>
            getr regs' 10 = w64 q /\ 4096 + HEAD <= q /\
            ablocks B ly' S' = ablocks B (d_ly d) (d_S d) ++ [(q - HEAD, dec_size (d_tb d) + HEAD)] /\
            fs_rblock tfibsegs B ly' S' W' mem' q (dec_size (d_tb d)) /\
            zbytes_at tfibsegs W' mem' q (WriterSpec.six_bytes six) /\
            wkeep tfibsegs (d_W d) W' (d_mem d) mem' (spZ (d_regs d)) (d_ot d) (d_lenp d) 8 /\
            val_mem tfibsegs (mrestrict (w_H W') mem') (d_lenp d) 8
              (Z.of_nat (length (WriterSpec.six_bytes six))) /\
            cstr_ok tfibsegs W' mem' (d_text d) (d_tb d) /\
            fs_glob tfibsegs W' mem' (d_live d + dec_size (d_tb d))
              (Z.max (d_peak d) (d_live d + dec_size (d_tb d))) ((d_cnt d + 1) mod 2 ^ 64) (d_fail d))))
  end.
  { eapply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok);
      [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity
      | rewrite R1F; exact HRET | exact HJ | exact HARU | exact HPRES |].
    intros mat2. cbn beta.
    split; [exact R10F|]. split; [exact Hq|]. split; [exact Hbl|].
    split.
    { pose proof Hrb as (RB1 & RB2 & RB3 & RB4). split; [exact RB1|]. split; [exact RB2|]. split; [exact RB3|].
      exact (val_mem_below (w_H Wc) mem2 (ms_mem ms) alloc_ceiling (q - HEAD) 8%nat (d_n d) SB
               ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia) RB4). }
    split.
    { unfold zbytes_at in HZb |- *. apply (garr8_frame tfibsegs _ _ q _ HZb).
      intros a Ha. apply (mbyte_below (w_H Wc) mem2 (ms_mem ms) alloc_ceiling a SB).
      pose proof (decLA_nbytes six (d_tb d) Hsix) as Hnb2. unfold d_n, HEAD in *. lia. }
    split.
    { intros a Ha Hno. change (spZ (d_regs d)) with (d_sp d) in Ha. destruct (Kw a Ha Hno) as [K1 K2].
      assert (HAV : aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a)
        by (apply (aview_at tfibsegs); apply FR; [lia | unfold DEC_F in *; lia]).
      split.
      - rewrite <- K1. apply (mbyte_of_aview tfibsegs). exact HAV.
      - etransitivity; [exact K2|].
        apply decLB_wr_eq; [lia | intros X; pose proof (fs_segs_img a X) as Hl; unfold FS_IMG_END in Hl; lia
                           | exact HAV]. }
    split; [exact VL|].
    split; [exact (cstr_ok_below Wc mem2 (ms_mem ms) (d_text d) (d_tb d) SB Kc)|].
    rewrite Z.mod_small by lia.
    exact (fs_glob_below Wc mem2 (ms_mem ms) _ _ _ _ SB Hglob). }
  eapply SRr_mono; [exact MAIN|].
  cbv beta. intros W' c' Hle HP. right. right.
  exists q, (WriterSpec.six_bytes six).
  split; [exact Hcf|]. split; [exact HSOME|]. split; [unfold HEAD in *; lia|]. exact HP.
Qed.

(* ---- the fake-frame placement (decode_spec_ff): *lenp is 8 bytes of a caller fake frame of the entry. The facts the
   success tail needs of it at a cut: its frame (for the store's awr_byte fr0 arm), its place (off the image and the
   shadow band), its shadow addressable (the entry's premise carried through the journal's frame clause), and its
   bytes writable (dec_kept's value, off the image) ---- *)
(* a shadow byte of a live frame's granule is not user-poisoned (it would be the shadow of a block granule) *)
Lemma decLN_ush_frame : forall ly S U (W : world tfibsegs) mem md cid pos lo x,
  AR tfibsegs B ly S W (unpoison U mem) md -> upoison_ok B ly S U -> In (cid, pos) (frames S) ->
  lo mod 8 = 0 -> (forall a, lo <= a < lo + 8 -> in_zr a (frame_rng ly (cid, pos))) -> lo <= x < lo + 8 ->
  in_ush U (shadow_of_addr SHADOW_OFF x) = false.
Proof.
intros ly S U W mem md cid pos lo x HAR HOK Hcp Hl8 Hfr Hx.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (in_ush U (shadow_of_addr SHADOW_OFF x)) eqn:EU; [exfalso|reflexivity].
destruct (ush_granule B ly S U _ HOK EU) as (g & p & m & Hblk & Hg8 & Hgs & Hgpb & Hgn).
pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison U mem) md p m cid pos HAR Hblk Hcp) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
pose proof (Hfr lo ltac:(lia)) as Hz. unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
pose proof (Z.mul_div_le (req_size m) 8 ltac:(lia)) as RQ3.
assert (Hg : g = lo).
{ unfold shadow_addr, shadow_of_addr in Hgs. clear - Hgs Hg8 Hl8 Hx. Z.div_mod_to_equations. lia. }
subst g. lia.
Qed.

Lemma decLN_lenp_ff : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  d_FP d = FS_PSTAT_FP ++ [(d_lenp d, d_lenp d + 8)] ->
  4096 <= d_lenp d /\ d_lenp d + 8 <= alloc_ceiling /\ d_lenp d mod 8 = 0 /\
  (exists cid pos, In (cid, pos) (frames (d_S d)) /\
     forall a, d_lenp d <= a < d_lenp d + 8 -> in_zr a (frame_rng lyc (cid, pos))) /\
  (d_lenp d + 8 <= 0x10000 \/ 0x5fd000 <= d_lenp d) /\
  (forall a, d_lenp d <= a < d_lenp d + 8 -> ~ in_img tfibsegs a /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)) /\
  range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF (d_lenp d) 8 /\
  (forall a, d_lenp d <= a < d_lenp d + 8 -> writable_at tfibsegs (mrestrict (w_H Wc) memc) a).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFP.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (decL_lenp_range B d HE) as (LR1 & LR2 & LR).
assert (LR3 : d_lenp d + 8 <= alloc_ceiling).
{ destruct LR as [(HFP' & _) | (_ & _ & H)]; [|exact H].
  exfalso. rewrite HFP in HFP'. apply (f_equal (@length (Z * Z))) in HFP'. rewrite length_app in HFP'.
  cbn [length] in HFP'. lia. }
clear LR.
pose proof HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hl8 & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
destruct HPL as [(HFP' & _) | (_ & _ & (cid & pos & Hcp & Hfr) & _ & HRA0)].
{ exfalso. rewrite HFP in HFP'. apply (f_equal (@length (Z * Z))) in HFP'. rewrite length_app in HFP'.
  cbn [length] in HFP'. lia. }
pose proof (proj1 (proj1 (proj1 HPRE))) as HAR0.
pose proof (proj1 (proj2 (proj1 HPRE))) as HUOK0.
decL_unhead HH.
pose proof HARU as (HARc & HUOKc & _).
pose proof HKe as (Kv & _).
unfold dec_J in HJ.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & JF & _).
cbn [app] in Hfrs.
assert (Hcpc : In (cid, pos) (frames Sc)) by (rewrite Hfrs; exact Hcp).
destruct (al_layout _ _ LAWS (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) (d_mem d)) (d_md d) lyc HAR0 Hly)
  as (_ & Hfa & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR0 Hcp) as (F32 & Fapp & _).
pose proof (Hfr (d_lenp d) ltac:(lia)) as I1. pose proof (Hfr (d_lenp d + 7) ltac:(lia)) as I2.
unfold in_zr, frame_rng in I1, I2. cbn [fst snd] in I1, I2.
assert (Hfrc : forall a, d_lenp d <= a < d_lenp d + 8 -> in_zr a (frame_rng lyc (cid, pos))).
{ intros a Ha. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa. lia. }
assert (NI : forall a, d_lenp d <= a < d_lenp d + 8 -> ~ in_img tfibsegs a).
{ intros a Ha. apply (frm_img tfibsegs B LAWS _ _ _ _ _ cid pos a HAR0 Hcp). lia. }
assert (NI2 : d_lenp d + 8 <= 0x10000 \/ 0x5fd000 <= d_lenp d).
{ destruct (Z_le_gt_dec (d_lenp d + 8) 0x10000) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec 0x5fd000 (d_lenp d)) as [H'|H']; [right; exact H'|].
  exfalso. apply (NI (Z.max (d_lenp d) 0x10000)); [lia|]. apply decLB_in_img. lia. }
assert (BAND : forall a, d_lenp d <= a < d_lenp d + 8 -> a < SHADOW_OFF \/ kHighMemBeg <= a).
{ intros a Ha. unfold in_app in Fapp. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
split; [exact LR1|]. split; [exact LR3|]. split; [exact Hl8|].
split; [exists cid, pos; split; [exact Hcp | exact Hfrc]|].
split; [exact NI2|].
split; [intros a Ha; split; [exact (NI a Ha) | exact (BAND a Ha)]|].
split.
{ apply (range_addressable_agree (aview tfibsegs (w_H (d_W d)) (d_mem d)) (aview tfibsegs (w_H Wc) memc) SHADOW_OFF
    (d_lenp d) 8); [|exact HRA0].
  intros x Hx.
  pose proof (decLN_sh_frame (frame_addr (d_ly d) cid pos) (fs_frame_bytes cid) (d_lenp d) x F32 Hl8
    ltac:(lia) ltac:(lia) Hx) as SH.
  pose proof (decLN_sh_bounds x ltac:(lia)) as SB.
  assert (Hs0 : 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64) by (unfold SHADOW_OFF in SB |- *; lia).
  rewrite <- (aview_unpoison_out tfibsegs (w_H Wc) Uc memc (shadow_of_addr SHADOW_OFF x))
    by (rewrite (wz _ Hs0); exact (decLN_ush_frame lyc Sc Uc Wc memc mdc cid pos (d_lenp d) x HARc HUOKc Hcpc Hl8 Hfrc Hx)).
  rewrite <- (aview_unpoison_out tfibsegs (w_H (d_W d)) (d_U d) (d_mem d) (shadow_of_addr SHADOW_OFF x))
    by (rewrite (wz _ Hs0); exact (decLN_ush_frame (d_ly d) (d_S d) (d_U d) (d_W d) (d_mem d) (d_md d) cid pos (d_lenp d) x
          HAR0 HUOK0 Hcp Hl8 Hfr Hx)).
  apply (JF cid pos _ Hcp).
  - right. unfold in_zr. cbn [fst snd]. exact SH.
  - rewrite HFP. pose proof (BAND (d_lenp d) ltac:(lia)) as B0. pose proof (BAND (d_lenp d + 7) ltac:(lia)) as B7.
    apply decLN_notFP; unfold SHADOW_OFF, kHighMemBeg in *; lia. }
intros a Ha.
pose proof (Kv (Z.to_nat (a - d_lenp d)) ltac:(lia)) as Hb.
rewrite Z2Nat.id in Hb by lia. replace (d_lenp d + (a - d_lenp d)) with a in Hb by lia.
unfold mbyte in Hb. destruct (mrestrict (w_H Wc) memc (Z_to_bv 64 a)) as [b|] eqn:Em.
- unfold mrestrict in Em. destruct (w_H Wc (Z_to_bv 64 a)) eqn:Eh; [discriminate Em|].
  apply (apresent_writable tfibsegs). split; [exact Eh | exists b; exact Em].
- exfalso. rewrite (seg_rom_none tfibsegs a ltac:(lia) (NI a Ha)) in Hb. discriminate Hb.
Qed.

(* ---- the success arm, decode_spec_ff's placement: lenp in a caller fake frame ---- *)
Lemma decLN_succ_ff : forall d q six pad acc Wc lyc Sc Uc regs2 mem2 md2 k,
  dec_entry_ok B d ->
  dec_head B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regs2 mem2 md2 k ->
  getr regs2 10 = w64 2 -> pad <= 2 -> WriterSpec.six_tail_ok six = true ->
  d_FP d = FS_PSTAT_FP ++ [(d_lenp d, d_lenp d + 8)] -> d_ot d = d_sp d ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regs2 (Z_to_bv 64 DEC_EXIT_PAD) mem2 (YK11.seg_rom tfibsegs)) md2)
    (dec_post B d).
Proof.
intros d q six pad acc Wc lyc Sc Uc regs2 mem2 md2 k HE HH R10 Hpad2 HTOK HFP Hot.
pose proof asan_consts as (C1 & _ & _ & _).
pose proof (decLB_sp B d HE) as (SP1 & SP2 & SP3).
pose proof (decLB_q B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regs2 mem2 md2 k HE HH)
  as (Q16 & Q1 & Q2 & Qn & _).
pose proof (decLB_lsite B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regs2 mem2 md2 k HE HH) as (_ & LS2 & LS).
pose proof (decLN_lenp_ff d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regs2 mem2 md2 k HE HH HFP)
  as (LP1 & LP2 & LP3 & (cid & pos & Hcp & Hfrc) & LNI2 & LNI & LRA & LW).
pose proof (decLN_atoms d q six pad acc Wc lyc Sc Uc regs2 mem2 md2 k [] HE HH ltac:(pose proof HH as HH1;
  decL_unhead HH1; lia)) as HGF.
pose proof HH as HH0. decL_unhead HH. unfold dec_J in HJ.
pose proof HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & Htb & _ & _ & _ & HDJ & _).
pose proof (proj1 HPRE) as ((_ & HRET & _) & _).
pose proof HKe as (Kv & Kw & Kc & Kr).
pose proof Hglob as (_ & _ & _ & _ & GL1 & GL2 & GL3 & GL4).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcnt & _).
set (E := decL_E d regs2 []) in *.
assert (E2 : bv_unsigned (ew E 2) = d_sp d - DEC_F)
  by (unfold E; rewrite (decL_E_reg d regs2 [] 2 2%bv eq_refl); exact Hsp).
assert (E9 : ew E 9 = Z_to_bv 64 q)
  by (unfold E; rewrite (decL_E_reg d regs2 [] 9 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E; rewrite (decL_E_reg d regs2 [] 21 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = Z_to_bv 64 (Z.of_nat (length (WriterSpec.six_bytes six))))
  by (unfold E; rewrite (decL_E_reg d regs2 [] 22 22%bv eq_refl); exact R22).
assert (E33 : ew E 33 = Z_to_bv 64 (d_lenp d)) by (unfold E; exact (decL_E_lenp d regs2 [])).
assert (E33u : bv_unsigned (ew E 33) = d_lenp d) by (rewrite E33; apply wz; lia).
pose proof (WriterSpecFacts.six_bytes_length six) as Hnb.
assert (Hn64 : 0 <= Z.of_nat (length (WriterSpec.six_bytes six)) < 2 ^ 64) by lia.
(* the symbolic state of the success tail and its shadow entry for *lenp *)
assert (HS : st_ok tfibsegs E (decLN_addf decL_lss_ff 10 (mkAF 2 2 0))
  (restrict (w_H Wc) (YK11.mkst regs2 (Z_to_bv 64 DEC_EXIT_PAD) mem2 (YK11.seg_rom tfibsegs)))).
{ apply decLN_add_atom;
    [| apply (decLN_af E 10%nat 2 2 2); [unfold E; rewrite (decL_E_reg d regs2 [] 10 10%bv eq_refl); exact R10
       | lia | lia]].
  unfold decL_lss_ff.
  apply (decL_build B HSS d Wc lyc Sc Uc regs2 mem2 md2 k [] DEC_EXIT_PAD [decL_lpr] decL_lgf_ff HE HJ HARU
    Hsp HFr HLs).
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold decL_lpr, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite E33u. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply LW. lia.
  - fold E. apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, decL_lpr, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E33u.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, DEC_F in *.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    pose proof LNI2 as LN. destruct LN as [LN|LN];
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  - unfold decL_lgf_ff. cbn [atoms_ok]. split; [|exact HGF].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite E33u.
    change (2 ^ 3) with 8. split; [lia | split; [exact LP3 | lia]]. }
assert (SHOK : sh_ok tfibsegs decL_Bx decL_lSH E (mrestrict (w_H Wc) mem2)).
{ unfold sh_ok, decL_lSH. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H Wc) mem2 E decL_Bx 33%nat (d_lenp d) 8 (d_lenp d) 0 8 LRA).
  - unfold decL_Bx. apply (U_atom E 21 SHADOW_OFF); [exact E21 | unfold SHADOW_OFF; lia].
  - apply (U_atom E 33 (d_lenp d)); [exact E33 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn in Hx. destruct (LNI x ltac:(lia)) as (_ & Hbd). unfold SHADOW_OFF, kHighMemBeg in *. lia. }
(* the run to the final `ret` 0x849bc *)
fsw_aj_run_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan.
- cbv [decLN_addf decL_lss_ff fss_retT ss_mem].
  apply (decLN_awr0 B E d [decL_lpr] _ _ _ _ E2 ltac:(lia)).
  eapply awr_ok_cons_gen with (k := 33%nat) (b := d_lenp d);
    [ reflexivity | exact E33u
    | cbv [decL_lpr YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; split;
      [ rewrite HFP; unfold inFP; exists (d_lenp d, d_lenp d + 8);
        split; [apply in_or_app; right; left; reflexivity | cbn [fst snd]; lia]
      | exists cid, pos; split; [exact Hcp | apply Hfrc; lia] ]
    | apply awr_ok_nil ].
- (* at the final `ret` 0x849bc: only the frame and *lenp were written *)
  subst k. subst Uc.
  assert (FR : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((d_sp d - DEC_F <= a < d_sp d) \/ (d_lenp d <= a < d_lenp d + 8)) ->
    ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
  { apply (decLN_frame_out E _ mem2 (ms_mem ms)
             (fun x => (d_sp d - DEC_F <= x < d_sp d) \/ (d_lenp d <= x < d_lenp d + 8)) HF).
    intros r a Hin Hr.
    cbv [decLN_addf decL_lss_ff fss_retT ss_mem fsT_ret_regions app In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbv [fstk_ret fs_got_region fs_bcell_region decL_lpr
           YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      [ rewrite E2 in Hr; left; unfold DEC_F in *; lia | lia | lia | rewrite E33u in Hr; right; lia ]. }
  (* below alloc_ceiling only *lenp was written *)
  assert (SBx : forall a, 0 <= a < alloc_ceiling -> ~ (d_lenp d <= a < d_lenp d + 8) ->
    ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a))
    by (intros a Ha Hn; apply FR; [lia | unfold DEC_F in *; lia]).
  assert (E46 : ew E 46 = getr (d_regs d) 1%bv)
    by (unfold E; change 46%nat with (34 + 12)%nat; rewrite (decLN_E_sav d regs2 [] 12%nat ltac:(lia));
        reflexivity).
  assert (E2w : ew E 2 = w64 (d_sp d - DEC_F))
    by (unfold w64; rewrite <- E2; symmetry; apply Z_to_bv_bv_unsigned).
  assert (R1F : getr (ms_regs ms) 1 = getr (d_regs d) 1)
    by (exact (decL_reg (w_H Wc) E _ ms 1%bv (SOff 46 0) _ HS ltac:(vm_compute; reflexivity)
                 ltac:(rewrite fsw_SOff0; exact E46))).
  assert (R10F : getr (ms_regs ms) 10 = w64 q)
    by (exact (decL_reg (w_H Wc) E _ ms 10%bv (SOff 9 0) _ HS ltac:(vm_compute; reflexivity)
                 ltac:(rewrite fsw_SOff0; exact E9))).
  (* the callee-saved registers: sp back up by the frame, s0..s11 and ra reloaded from the frame words *)
  assert (HPRES : aregs_preserved (d_regs d) (ms_regs ms)).
  { lazymatch type of HS with
    | st_ok _ _ ?ssf _ =>
      apply (fsw_preserved (w_H Wc) E ssf ms (d_regs d) (fun r : bv 5 => sr_get (ss_regs ssf) r) HS);
      [vm_compute; reflexivity|];
      let r := fresh "r" in let Hr := fresh "Hr" in
      intros r Hr; cbv [CALLEE_SAVED In] in Hr;
      repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]
    end; cbv beta;
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
    - rewrite (decL_soff E 2 112 (d_sp d - DEC_F) E2w ltac:(unfold DEC_F in *; lia) ltac:(unfold DEC_F in *; lia)).
      replace (d_sp d - DEC_F + 112) with (d_sp d) by (unfold DEC_F; lia).
      unfold w64, d_sp, spZ. apply Z_to_bv_bv_unsigned.
    - rewrite fsw_SOff0. unfold E. rewrite (decL_E_reg d regs2 [] 3 3%bv eq_refl). exact R3.
    - rewrite fsw_SOff0. unfold E. rewrite (decL_E_reg d regs2 [] 4 4%bv eq_refl). exact R4.
    - rewrite fsw_SOff0. unfold E. change 45%nat with (34 + 11)%nat.
      rewrite (decLN_E_sav d regs2 [] 11%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 44%nat with (34 + 10)%nat.
      rewrite (decLN_E_sav d regs2 [] 10%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 43%nat with (34 + 9)%nat.
      rewrite (decLN_E_sav d regs2 [] 9%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 42%nat with (34 + 8)%nat.
      rewrite (decLN_E_sav d regs2 [] 8%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 41%nat with (34 + 7)%nat.
      rewrite (decLN_E_sav d regs2 [] 7%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 40%nat with (34 + 6)%nat.
      rewrite (decLN_E_sav d regs2 [] 6%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 39%nat with (34 + 5)%nat.
      rewrite (decLN_E_sav d regs2 [] 5%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 38%nat with (34 + 4)%nat.
      rewrite (decLN_E_sav d regs2 [] 4%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 37%nat with (34 + 3)%nat.
      rewrite (decLN_E_sav d regs2 [] 3%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 36%nat with (34 + 2)%nat.
      rewrite (decLN_E_sav d regs2 [] 2%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 35%nat with (34 + 1)%nat.
      rewrite (decLN_E_sav d regs2 [] 1%nat ltac:(lia)). reflexivity.
    - rewrite fsw_SOff0. unfold E. change 34%nat with (34 + 0)%nat.
      rewrite (decLN_E_sav d regs2 [] 0%nat ltac:(lia)). reflexivity. }
  (* the stored length, read back from the region of *lenp *)
  assert (VL : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) (d_lenp d) 8
                 (Z.of_nat (length (WriterSpec.six_bytes six)))).
  { lazymatch type of HS with
    | st_ok _ _ ?ssf _ =>
      pose proof (fsw_region_nth E ssf (restrict (w_H Wc) ms) 3%nat
        (YP09.mkRegion (Some 33%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 22 0))]) HS
        ltac:(vm_compute; reflexivity)) as HR3
    end.
    cbn [ms_mem restrict] in HR3.
    rewrite <- (Z.add_0_r (d_lenp d)).
    apply (fsw_field E _ 33%nat (d_lenp d) [YP09.mkChunk 0 (CVal 8 (SOff 22 0))] 0 8 0 8 0 8%N (SOff 22 0) _ HR3
             E33u);
      [ cbv [In]; tauto | rewrite fsw_SOff0; exact E22 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia ]. }
  assert (HSOME : WriterSpec.b64_dec (d_tb d) = Some (WriterSpec.six_bytes six)).
  { assert (HDEC : WriterSpec.b64_dec (d_tb d) = decLA_out pad six (skipn (length (d_tb d)) (d_tb d)))
      by exact Hscan.
    rewrite decLA_skipn_end, decLA_out_nil in HDEC.
    rewrite HDEC, HTOK. replace (pad <=? 2) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg _ ?mdX) _ =>
    assert (MAIN : SRr tfibsegs Wc (mkCfg ms mdX)
      (fpostU tfibsegs B (d_STKJ d) (d_ot d) (d_FP d) (d_regs d) (d_ly d) (d_S d) (d_U d) (d_W d) (d_mem d)
         (d_md d) 1 (d_U d ++ [(q - HEAD, HEAD)])
         (fun (ly' : alayout) (S' : astate) (W' : world tfibsegs) (regs' : bvmap 5 word)
              (mem' : word -> option byte) (md' : Model) =>
            getr regs' 10 = w64 q /\ 4096 + HEAD <= q /\
            ablocks B ly' S' = ablocks B (d_ly d) (d_S d) ++ [(q - HEAD, dec_size (d_tb d) + HEAD)] /\
            fs_rblock tfibsegs B ly' S' W' mem' q (dec_size (d_tb d)) /\
            zbytes_at tfibsegs W' mem' q (WriterSpec.six_bytes six) /\
            wkeep tfibsegs (d_W d) W' (d_mem d) mem' (spZ (d_regs d)) (d_ot d) (d_lenp d) 8 /\
            val_mem tfibsegs (mrestrict (w_H W') mem') (d_lenp d) 8
              (Z.of_nat (length (WriterSpec.six_bytes six))) /\
            cstr_ok tfibsegs W' mem' (d_text d) (d_tb d) /\
            fs_glob tfibsegs W' mem' (d_live d + dec_size (d_tb d))
              (Z.max (d_peak d) (d_live d + dec_size (d_tb d))) ((d_cnt d + 1) mod 2 ^ 64) (d_fail d))))
  end.
  { eapply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok);
      [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity
      | rewrite R1F; exact HRET | exact HJ | exact HARU | exact HPRES |].
    intros mat2. cbn beta.
    split; [exact R10F|]. split; [exact Hq|]. split; [exact Hbl|].
    split.
    { pose proof Hrb as (RB1 & RB2 & RB3 & RB4). split; [exact RB1|]. split; [exact RB2|]. split; [exact RB3|].
      apply (decLB_val_mem (w_H Wc) mem2 (ms_mem ms) (q - HEAD) 8 (d_n d)); [|exact RB4].
      intros kk Hk. apply aview_at. apply SBx; [unfold HEAD in *; lia|].
      intros Hl. apply (proj2 (LS _ Hl)). unfold HEAD in *. lia. }
    split.
    { unfold zbytes_at in HZb |- *. apply (garr8_frame tfibsegs _ _ q _ HZb).
      intros a Ha. pose proof (decLA_nbytes six (d_tb d) Hsix) as Hnb2.
      apply (mbyte_of_aview tfibsegs). apply aview_at. apply SBx; [unfold d_n, HEAD in *; lia|].
      intros Hl. apply (proj2 (LS a Hl)). unfold d_n, HEAD in *. lia. }
    split.
    { (* ot = sp: the window [sp, ot) is empty *)
      intros a Ha Hno. exfalso. rewrite Hot in Ha. change (spZ (d_regs d)) with (d_sp d) in Ha. lia. }
    split; [exact VL|].
    split.
    { apply (decLB_cstr_agree Wc mem2 (ms_mem ms) (d_text d) (d_tb d)); [| |exact Kc].
      - intros a Ha. pose proof Kc as (_ & Kt0 & Ktc & _).
        pose proof (Z.div_mod (d_text d + Z.of_nat (length (d_tb d))) 8 ltac:(lia)) as Hdm.
        pose proof (Z.mod_pos_bound (d_text d + Z.of_nat (length (d_tb d))) 8 ltac:(lia)) as Hm.
        pose proof (Z.div_mod (d_lenp d) 8 ltac:(lia)) as Hdl.
        (* the word holding the NUL ends at or below alloc_ceiling, which is 4096-aligned (YM05.alloc_ceiling_value) *)
        pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as Hda.
        pose proof (proj2 YM05.alloc_ceiling_value) as Hac.
        apply aview_at. apply SBx; [lia|]. intros Hl. lia.
      - intros a Ha. apply aview_at. apply SBx; [unfold SHADOW_OFF, kHighMemBeg in *; lia|].
        intros Hl. destruct (LNI a Hl) as (_ & Hbd). unfold SHADOW_OFF, kHighMemBeg in *. lia. }
    rewrite Z.mod_small by lia.
    revert Hglob. unfold fs_glob, fs_glob_at, d_n. intros (G1 & G2 & G3 & G4 & GR).
    assert (VX : forall a v, 0x10000 <= a -> a + 8 <= 0x5fd000 ->
      val_mem tfibsegs (mrestrict (w_H Wc) mem2) a 8 v -> val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a 8 v).
    { intros a v Ha1 Ha2 Hv. apply (decLB_val_mem (w_H Wc) mem2 (ms_mem ms) a 8 v); [|exact Hv].
      intros kk Hk. apply aview_at. apply SBx; [lia|]. intros Hl. lia. }
    unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
    split; [apply VX; [lia | lia | exact G1]|].
    split; [apply VX; [lia | lia | exact G2]|].
    split; [apply VX; [lia | lia | exact G3]|].
    split; [apply VX; [lia | lia | exact G4]|].
    exact GR. }
  eapply SRr_mono; [exact MAIN|].
  cbv beta. intros W' c' Hle HP. right. right.
  exists q, (WriterSpec.six_bytes six).
  split; [exact Hcf|]. split; [exact HSOME|]. split; [unfold HEAD in *; lia|]. exact HP.
Qed.

(* ==== the two lemmas of the contract ((internal path)), statements VERBATIM ==== *)
(* decode_spec's placement (lenp on the caller's real stack): NO premise-gap hypothesis may be used here *)
Lemma decL_arm_nul_rs : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  i = length (d_tb d) -> d_FP d = FS_PSTAT_FP ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs)) mdc) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE Hi HFP. subst i.
apply (decLN_exit d q six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE).
intros regs' mem' md' HH' R10 Hpad2 HTOK.
exact (decLN_succ_rs d q six pad acc Wc lyc Sc Uc regs' mem' md' k HE HH' R10 Hpad2 HTOK HFP).
Qed.

Lemma decL_arm_nul : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  i = length (d_tb d) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs)) mdc) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE Hi. subst i.
destruct (decL_lenp_range B d HE) as (_ & _ & [(HFP & _ & _) | (HFP & Hot & _)]).
- exact (decL_arm_nul_rs d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE eq_refl HFP).
- apply (decLN_exit d q six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE).
  intros regs' mem' md' HH' R10 Hpad2 HTOK.
  exact (decLN_succ_ff d q six pad acc Wc lyc Sc Uc regs' mem' md' k HE HH' R10 Hpad2 HTOK HFP Hot).
Qed.

End L5.
