(* fs program part, lane ENTRY, segment S3 + S4 of the LLVMFuzzerTestOneInput walk (fs.asan 0x81024-0x8104c, fs.c:322-323):
   from the return of memchr(data, 0, size) (0x81024, boundary C1) to the epilogue (0x81110, boundary C9: the
   `n > 3 MiB` branch at 0x8103c) and to the return of check_no_overread(data, n) (0x8104c, boundary C2).
   rule 24: no function proved here (fs's own harness entry; donor cgif_file_fuzzer form).
   Head (fe3_seg3_head): `beqz a0` (0x81024) is split by SRr_sym_branch (a0 = 0 iff the payload has no NUL), the run
   does `sub s3, a0, s4` (s3 = the strnlen fe_n), `sb zero, 4(s9)` and `sd -1, 32(s8)` (len), and stops at the `bltu`
   (0x8103c); there the canonical state is rebuilt (FSW_entry_canon.fe_canon) as this file's inner boundary
   fe_ss PC_s3mid [fe_len_lit (-1)] / INV_S3mid. Tail (fe3_seg3_tail): the `bltu` is split on n. Taken (n > 3 MiB): the
   run reaches PC_epi (C9). Not taken: the run reaches check_no_overread, a PROGRAM call: fpreU from the walk's journal
   by YCbq.afn_pre_at (FP = FS_PSTAT_FP, own = the class-0 frame), the callee's chain the entry's frame record pushed
   on the entry's empty chain (YCbq.achain_push), the spec en_no_overread, its fpostU journal composed onto the walk's
   by FSW_K3.fsw_ajournal_sub4 (the statics arm), the canonical state rebuilt at the return (C2).
   Form: FSW_entry_defs.v fe_from (donor cgif_file_fuzzer lib/A/ACf5.v:73-84 rt_from); the program call follows
   FSW_ret.v:180-196 fsw_fpreU_at with the walk's own FP and fake frame. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_frame FSW_K3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
ACfn FSH_Harness FSH_Fn_entry FSH_Fn_cno FSW_entry_defs FSW_entry_canon FSW_entry_ar FSW_pstat_store FSW_strkit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require ACem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- zfind (FSH_Gen.v): None means no c in l; Some j the first c ---- *)
Lemma fe3_zfind_none : forall c l, zfind c l = None -> ~ In c l.
Proof.
intros c l. induction l as [|x t IH]; cbn [zfind In]; [intros _ H; exact H|].
destruct (Z.eqb_spec x c) as [->|Hx]; intros H; [discriminate H|].
destruct (zfind c t) eqn:E; [discriminate H|].
intros [->|Hin]; [exact (Hx eq_refl) | exact (IH eq_refl Hin)].
Qed.
Lemma fe3_zfind_some : forall c l j, zfind c l = Some j ->
  (j < length l)%nat /\ nth j l 0 = c /\ ~ In c (firstn j l).
Proof.
intros c l. induction l as [|x t IH]; intros j; cbn [zfind]; [discriminate|].
destruct (Z.eqb_spec x c) as [->|Hx]; intros H.
- injection H as <-. cbn [length nth firstn In]. split; [lia|]. split; [reflexivity | tauto].
- destruct (zfind c t) as [j'|] eqn:E; cbn [option_map] in H; [|discriminate H].
  injection H as <-. destruct (IH j' eq_refl) as (H1 & H2 & H3).
  cbn [length nth firstn In]. split; [lia|]. split; [exact H2|].
  intros [->|Hin]; [exact (Hx eq_refl) | exact (H3 Hin)].
Qed.

(* the strnlen n and the text it cuts (FSW_entry_defs.v fe_n / fe_tb) *)
Lemma fe3_n_facts : forall cx, c_n cx = Z.of_nat (length (c_pl cx)) ->
  0 <= fe_n cx <= c_n cx /\ Z.of_nat (length (fe_tb cx)) = fe_n cx /\ Forall (fun v => v <> 0) (fe_tb cx) /\
  (forall j, (j < length (fe_tb cx))%nat -> nth j (fe_tb cx) 0 = nth j (fe_bytes cx) 0).
Proof.
intros cx Hn. unfold fe_tb, fe_n.
assert (Hl : length (fe_bytes cx) = length (c_pl cx)) by (unfold fe_bytes; apply length_map).
destruct (zfind 0 (fe_bytes cx)) as [j|] eqn:Ez; cbv iota beta.
- destruct (fe3_zfind_some 0 (fe_bytes cx) j Ez) as (H1 & _ & H3).
  rewrite Nat2Z.id. rewrite length_firstn.
  split; [lia|]. split; [lia|]. split.
  + apply Forall_forall. intros v Hv Hv0. subst v. exact (H3 Hv).
  + intros i Hi. rewrite nth_firstn.
    destruct (Nat.ltb_spec i j); [reflexivity | lia].
- pose proof (fe3_zfind_none 0 (fe_bytes cx) Ez) as H0.
  rewrite Hn, Nat2Z.id, <- Hl, firstn_all.
  split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
  apply Forall_forall. intros v Hv Hv0. subst v. exact (H0 Hv).
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis en_no_overread : @check_no_overread_spec fx rc SK tfibsegs B.

Lemma fe3_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] l X. unfold same_io. cbn. repeat split; reflexivity. Qed.

(* the entry facts the segment reads (fe_base: tfib_lib_pre_x's afn_pre, the payload, the counts) *)
Lemma fe3_base_facts : forall cx, fe_base B cx ->
  fe_sp0 cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= fe_sp0 cx /\ fe_sp0 cx <= ly_top (c_ly cx) /\
  ly_top (c_ly cx) <= 2 ^ 47 /\
  raZ (c_regs cx) = RA_LLVMF /\ YK11.getr (c_regs cx) 3%bv = w64 (as_gp B) /\
  YK11.getr (c_regs cx) 4%bv = w64 (as_tp B) /\
  achain (c_ly cx) (aview tfibsegs (w_H (c_W cx)) (c_mem cx)) (fe_sp0 cx) (s0Z (c_regs cx)) [] /\
  frames (c_S cx) = [] /\ st_nev (c_S cx) + EV_LIB <= EV_MAX /\ blocks_bytes (c_S cx) + ACfn.LIVE_LIB <= LIVE_MAX /\
  ((c_n cx = 0 /\ c_p cx = A_EMPTY) \/ (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))) /\
  c_n cx = Z.of_nat (length (c_pl cx)) /\
  garr8 tfibsegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx) (fe_bytes cx) /\
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H (c_W cx)) (c_mem cx)) /\
  0 <= c_cnt cx /\ c_cnt cx + FS_CNT_LIB < 2 ^ 63.
Proof.
intros cx (Hpre & _ & Hc0 & Hcm & _).
destruct Hpre as (Hafn & Hra & _ & _ & Hpn & Hlen & Hgarr & Hfr & Hnev & Hbb & Hro & _).
destruct Hafn as (_ & _ & _ & Hgp & Htp & Hstk & _ & Hch & _).
destruct Hstk as (Hal & Hs0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold fe_sp0.
split; [exact Hal|]. split; [lia|]. split; [exact Htop|]. split; [lia|]. split; [exact Hra|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch|]. split; [exact Hfr|]. split; [exact Hnev|].
split; [exact Hbb|]. split; [exact Hpn|]. split; [exact Hlen|]. split; [exact Hgarr|]. split; [exact Hro|].
split; [exact Hc0 | exact Hcm].
Qed.

(* the boundary between the two halves of the segment: the `bltu` at 0x8103c, every register an atom (fe_canon), the
   frame's len = -1 and its shadow byte 0 (fe_lensh, `sb zero, 4(s9)` at 0x8102c); a1 = 3 MiB, s3 = n, s4 = data, s6 =
   the shadow base *)
Definition PC_s3mid : Z := 0x8103c.
Definition INV_S3mid : fe_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
    U3 = [] /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\ st_nev S3 = st_nev (c_S cx) /\
    blocks_bytes S3 = blocks_bytes (c_S cx) /\ fe_common cx k S3 W3 ms3 md3 0 /\ fe_regs_core cx E /\
    ew E 11 = Z_to_bv 64 (3 * 2 ^ 20) /\ ew E 19 = Z_to_bv 64 (fe_n cx) /\ ew E 20 = Z_to_bv 64 (c_p cx) /\
    ew E 22 = Z_to_bv 64 SHADOW_OFF /\ fs_stat tfibsegs W3 (ms_mem ms3) (c_live cx) (c_cnt cx) /\
    fe_lensh cx W3 (ms_mem ms3).

(* ---- the layout at a boundary: the walk's journal from the entry (own = the class-0 frame) and the payload ---- *)
Lemma fe3_geo : forall cx k ly3 S3 W3 mem3 md3,
  fe_base B cx ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 W3 mem3 md3 k ->
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ->
  frames S3 = [(0, c_fpos cx)] /\ ly_F ly3 = ly_F (c_ly cx) /\ ly_top ly3 = ly_top (c_ly cx) /\
  frame_addr ly3 0 (c_fpos cx) = fe_F cx /\ flag_addr ly3 0 (c_fpos cx) = fe_FL cx /\
  fe_F cx mod 32 = 0 /\ 4096 <= fe_F cx /\ fe_F cx + 64 <= alloc_ceiling /\
  4096 <= fe_FL cx < alloc_ceiling /\
  kLowMemEnd <= fe_SF cx /\ fe_SF cx + 8 <= kHighMemBeg /\
  (forall a, inFP FS_PSTAT_FP a -> ~ (fe_F cx <= a < fe_F cx + 64) /\ ~ (fe_SF cx <= a < fe_SF cx + 8) /\
     ~ (fe_sp0 cx - 88 <= a < fe_sp0 cx)) /\
  (forall i, 0 <= i < c_n cx -> 0 <= c_p cx + i < 2 ^ 64 /\ ~ (fe_F cx <= c_p cx + i < fe_F cx + 64) /\
     ~ (fe_SF cx <= c_p cx + i < fe_SF cx + 8) /\ ~ (fe_sp0 cx - 88 <= c_p cx + i < fe_sp0 cx) /\
     ~ inFP FS_PSTAT_FP (c_p cx + i)) /\
  (0 < c_n cx -> 4096 <= c_p cx /\ c_p cx + c_n cx + 8 <= alloc_ceiling /\ In (c_p cx, c_n cx) (ablocks B ly3 S3)).
Proof.
intros cx k ly3 S3 W3 mem3 md3 Hbase HJ Hab.
pose proof (fe3_base_facts cx Hbase) as (Hal & Hsp & Htop & H47 & _ & _ & _ & _ & Hfr & _ & _ & Hpn & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (EF : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (ET : ly_top ly3 = ly_top (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _); exact ET).
assert (Hfr3 : frames S3 = [(0, c_fpos cx)]) by (rewrite Hfrs, Hfr; reflexivity).
assert (Hin : In (0, c_fpos cx) (frames S3)) by (rewrite Hfr3; left; reflexivity).
assert (EFa : frame_addr ly3 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite EF; reflexivity).
assert (EFl : flag_addr ly3 0 (c_fpos cx) = fe_FL cx) by (unfold fe_FL, flag_addr; rewrite EF; reflexivity).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 0 (c_fpos cx) HAR Hin) as (Hal32 & Happ & _ & _).
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 mem3 md3 0 (c_fpos cx) HAR Hin) as (H4096 & Hfc & _).
destruct (al_flag _ _ LAWS ly3 S3 W3 mem3 md3 0 (c_fpos cx) HAR Hin) as (_ & _ & Hflapp & Hflc).
rewrite EFa in Hal32, Happ, H4096, Hfc. rewrite EFl in Hflapp, Hflc.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in Happ, Hfc.
assert (ESF : fe_SF cx = shadow_addr (fe_F cx)) by reflexivity.
pose proof (shadow_addr_bounds (fe_F cx) ltac:(unfold kHighMemEnd in *; lia)) as (Hs1 & Hs2).
assert (Hs3 : fe_SF cx + 8 <= kHighMemBeg).
{ rewrite ESF. unfold shadow_addr, SHADOW_OFF, kHighMemBeg.
  assert (fe_F cx / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). lia. }
rewrite <- ESF in Hs1.
split; [exact Hfr3|]. split; [exact EF|]. split; [exact ET|]. split; [exact EFa|]. split; [exact EFl|].
split; [exact Hal32|]. split; [exact H4096|]. split; [exact Hfc|].
split; [unfold in_app, app_addr in Hflapp; lia|].
split; [exact Hs1|]. split; [exact Hs3|].
split; [|split].
- intros a Ha. pose proof (pstat_bounds a Ha) as Hb.
  split; [|split].
  + intros Hr. apply (frm_img tfibsegs B LAWS ly3 S3 W3 mem3 md3 0 (c_fpos cx) a HAR Hin);
      [rewrite EFa, Hfb; exact Hr | apply fs_rw3_img; exact Hb].
  + lia.
  + unfold LLVMF_STK in Hsp. lia.
- intros i Hi. destruct Hpn as [(Hn0 & _) | (Hn & Hpin)]; [lia|].
  rewrite <- Hab in Hpin.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hpin) as (_ & Hp4096 & Hpc & Hpapp & _).
  assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hrq in Hpc, Hpapp.
  pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 mem3 md3 _ _ 0 (c_fpos cx) HAR Hpin Hin) as Hd.
  rewrite EFa, Hfb, Hrq in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  split; [lia|]. split; [lia|]. split.
  + unfold in_app, kLowShadowBeg, ASAN_CEIL in Hpapp. lia.
  + split; [unfold LLVMF_STK in Hsp; lia|].
    intros Hf. apply (blk_img tfibsegs B LAWS ly3 S3 W3 mem3 md3 _ _ (c_p cx + i) HAR Hpin);
      [rewrite Hrq; lia | apply fs_rw3_img, pstat_bounds, Hf].
- intros Hn. destruct Hpn as [(Hn0 & _) | (_ & Hpin)]; [lia|]. rewrite <- Hab in Hpin.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hpin) as (_ & Hp4096 & _).
  pose proof (fe_block_room B ly3 S3 W3 mem3 md3 _ _ HAR Hpin) as Hroom.
  assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hrq in Hroom. split; [exact Hp4096|]. split; [exact Hroom | exact Hpin].
Qed.

(* ---- what a run over the canonical regions writes: the frame, its shadow, the saved words ---- *)
Lemma fe3_frame_keep : forall E cs m m' (x : word),
  frame_of E (fe_regions cs) m m' ->
  ~ (bv_unsigned (ew E 24) <= bv_unsigned x < bv_unsigned (ew E 24) + 64) ->
  ~ (bv_unsigned (ew E 25) <= bv_unsigned x < bv_unsigned (ew E 25) + 8) ->
  ~ (bv_unsigned (ew E 8) - 88 <= bv_unsigned x < bv_unsigned (ew E 8)) ->
  m' x = m x.
Proof.
intros E cs m m' x HF N1 N2 N3. apply HF. intros (r & Hin & Hr).
unfold fe_regions in Hin. destruct Hin as [<-|[<-|[<-|[]]]];
  unfold fe_frame_region, fe_shadow_region, fs_ret_s0_region in Hr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.
Lemma fe3_aview_keep : forall cx E cs H m m' a,
  frame_of E (fe_regions cs) (mrestrict H m) (mrestrict H m') ->
  bv_unsigned (ew E 24) = fe_F cx -> bv_unsigned (ew E 25) = fe_SF cx -> bv_unsigned (ew E 8) = fe_sp0 cx ->
  0 <= a < 2 ^ 64 ->
  ~ (fe_F cx <= a < fe_F cx + 64) -> ~ (fe_SF cx <= a < fe_SF cx + 8) -> ~ (fe_sp0 cx - 88 <= a < fe_sp0 cx) ->
  aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros cx E cs H m m' a HF E24 E25 E8 Ha N1 N2 N3. apply aview_eq_of.
apply (fe3_frame_keep E cs); [exact HF | | |]; rewrite (wz a Ha); [rewrite E24 | rewrite E25 | rewrite E8]; assumption.
Qed.
Lemma fe3_pstat_in : forall g, In g [G_FAIL; G_LIVE; G_PEAK; G_COUNT] -> In (g, g + 8) FS_PSTAT_FP.
Proof.
intros g Hg. cbn [In] in Hg. unfold FS_PSTAT_FP.
destruct Hg as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; repeat (first [left; reflexivity | right]).
Qed.
Lemma fe3_stat_keep : forall (W : world tfibsegs) m m' live cnt,
  (forall a, inFP FS_PSTAT_FP a -> mrestrict (w_H W) m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a)) ->
  fs_stat tfibsegs W m live cnt -> fs_stat tfibsegs W m' live cnt.
Proof.
intros W m m' live cnt Hk (peak & G1 & G2 & G3 & G4 & R). exists peak.
assert (K : forall g v, In g [G_FAIL; G_LIVE; G_PEAK; G_COUNT] ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg Hv k0 Hk0. unfold mbyte.
  rewrite (Hk (g + Z.of_nat k0)) by (apply (inFP_FS_PSTAT_FP g (fe3_pstat_in g Hg)); lia). exact (Hv k0 Hk0). }
split; [apply K; [cbn; tauto | exact G1]|]. split; [apply K; [cbn; tauto | exact G2]|].
split; [apply K; [cbn; tauto | exact G3]|]. split; [apply K; [cbn; tauto | exact G4]|]. exact R.
Qed.

(* ---- the canonical state rebuilt at the machine state a run reached (fe_canon), from the run's symbolic state ---- *)
Lemma fe3_reg_at : forall E ss ms (H : word -> bool) (r : bv 5) n,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> YK11.getr (ms_regs ms) r = ew E n.
Proof. intros E ss ms H r n HS Hr. rewrite <- fsw_SOff0, <- Hr. exact (st_ok_reg tfibsegs E ss (restrict H ms) r HS). Qed.
Definition fe3_atoms_kept (ss : sstate) : Prop :=
  sr_get (ss_regs ss) 2%bv = SOff 2 0 /\ sr_get (ss_regs ss) 3%bv = SOff 3 0 /\ sr_get (ss_regs ss) 4%bv = SOff 4 0 /\
  sr_get (ss_regs ss) 8%bv = SOff 8 0 /\ sr_get (ss_regs ss) 9%bv = SOff 9 0 /\
  sr_get (ss_regs ss) 18%bv = SOff 18 0 /\ sr_get (ss_regs ss) 24%bv = SOff 24 0 /\
  sr_get (ss_regs ss) 25%bv = SOff 25 0 /\ sr_get (ss_regs ss) 26%bv = SOff 26 0 /\
  sr_get (ss_regs ss) 27%bv = SOff 27 0.
(* the registers of fe_regs_core from a machine register file that holds them *)
Lemma fe3_core_of_regs : forall cx regs xs,
  YK11.getr regs 8%bv = Z_to_bv 64 (fe_sp0 cx) -> YK11.getr regs 9%bv = Z_to_bv 64 (fe_sp1 cx) ->
  YK11.getr regs 2%bv = Z_to_bv 64 (fe_sp1 cx) -> YK11.getr regs 18%bv = Z_to_bv 64 (fe_F cx) ->
  YK11.getr regs 24%bv = Z_to_bv 64 (fe_F cx) -> YK11.getr regs 25%bv = Z_to_bv 64 (fe_SF cx) ->
  YK11.getr regs 3%bv = YK11.getr (c_regs cx) 3%bv -> YK11.getr regs 4%bv = YK11.getr (c_regs cx) 4%bv ->
  YK11.getr regs 26%bv = YK11.getr (c_regs cx) 26%bv -> YK11.getr regs 27%bv = YK11.getr (c_regs cx) 27%bv ->
  fe_regs_core cx (Ereg regs (fe_extra cx ++ xs)).
Proof.
intros cx regs xs R8 R9 R2 R18 R24 R25 R3 R4 R26 R27. unfold fe_regs_core.
rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl), (ew_Ereg_nat regs _ 9 9%bv eq_refl), (ew_Ereg_nat regs _ 2 2%bv eq_refl),
  (ew_Ereg_nat regs _ 18 18%bv eq_refl), (ew_Ereg_nat regs _ 24 24%bv eq_refl), (ew_Ereg_nat regs _ 25 25%bv eq_refl),
  (ew_Ereg_nat regs _ 3 3%bv eq_refl), (ew_Ereg_nat regs _ 4 4%bv eq_refl), (ew_Ereg_nat regs _ 26 26%bv eq_refl),
  (ew_Ereg_nat regs _ 27 27%bv eq_refl).
repeat split; assumption.
Qed.
Lemma fe3_core_after : forall cx E ss ms H xs,
  st_ok tfibsegs E ss (restrict H ms) -> fe3_atoms_kept ss -> fe_regs_core cx E ->
  fe_regs_core cx (Ereg (ms_regs ms) (fe_extra cx ++ xs)) /\
  YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (fe_sp0 cx) /\ YK11.getr (ms_regs ms) 24%bv = Z_to_bv 64 (fe_F cx) /\
  YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 (fe_F cx) /\ YK11.getr (ms_regs ms) 25%bv = Z_to_bv 64 (fe_SF cx).
Proof.
intros cx E ss ms H xs HS (A2 & A3 & A4 & A8 & A9 & A18 & A24 & A25 & A26 & A27)
  (C8 & C9 & C2 & C18 & C24 & C25 & C3 & C4 & C26 & C27).
assert (R8 : YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (fe_sp0 cx)) by (rewrite (fe3_reg_at E ss ms H 8%bv 8 HS A8); exact C8).
assert (R24 : YK11.getr (ms_regs ms) 24%bv = Z_to_bv 64 (fe_F cx)) by (rewrite (fe3_reg_at E ss ms H 24%bv 24 HS A24); exact C24).
assert (R18 : YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 (fe_F cx)) by (rewrite (fe3_reg_at E ss ms H 18%bv 18 HS A18); exact C18).
assert (R25 : YK11.getr (ms_regs ms) 25%bv = Z_to_bv 64 (fe_SF cx)) by (rewrite (fe3_reg_at E ss ms H 25%bv 25 HS A25); exact C25).
split; [|split; [exact R8|]; split; [exact R24|]; split; [exact R18 | exact R25]].
apply fe3_core_of_regs.
- exact R8.
- rewrite (fe3_reg_at E ss ms H 9%bv 9 HS A9). exact C9.
- rewrite (fe3_reg_at E ss ms H 2%bv 2 HS A2). exact C2.
- exact R18.
- exact R24.
- exact R25.
- rewrite (fe3_reg_at E ss ms H 3%bv 3 HS A3). exact C3.
- rewrite (fe3_reg_at E ss ms H 4%bv 4 HS A4). exact C4.
- rewrite (fe3_reg_at E ss ms H 26%bv 26 HS A26). exact C26.
- rewrite (fe3_reg_at E ss ms H 27%bv 27 HS A27). exact C27.
Qed.
(* the saved words' chunks under another env with the same extra atoms *)
Lemma fe3_sv_ok : forall cx E E' m,
  fe_E cx E -> fe_E cx E' ->
  Forall (YP09.chunk_ok tfibsegs E m (fe_sp0 cx)) fe_sv_chunks ->
  Forall (YP09.chunk_ok tfibsegs E' m (fe_sp0 cx)) fe_sv_chunks.
Proof.
intros cx E E' m HE HE' H. apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) H c Hc) as Hck.
unfold fe_sv_chunks in Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
intros i Hi. destruct (Hck i Hi) as (bt & H1 & H2). exists bt. split; [|exact H2].
rewrite <- H1. cbn [YP09.c_val YP09.c_off cbyte]. rewrite !fsw_SOff0.
change (33 + j)%nat with (32 + (1 + j))%nat. rewrite (HE (1 + j)%nat), (HE' (1 + j)%nat) by lia. reflexivity.
Qed.
(* the frame's flag word, from the frame region's chunk at 56 *)
Lemma fe3_flag_ok : forall cx E H mem fcs,
  fe_E cx E -> region_ok tfibsegs E (mrestrict H mem) (YP09.mkRegion (Some 24%nat) 0 64 0 64 fcs) ->
  bv_unsigned (ew E 24) = fe_F cx -> In (YP09.mkChunk 56 (CVal 8 (SOff 44 0))) fcs ->
  0 <= fe_FL cx < 2 ^ 64 ->
  rdword (aview tfibsegs H mem) (fe_F cx + 56) = Some (fe_FL cx).
Proof.
intros cx E H mem fcs HE Hr H24 Hin HFL.
apply ACem.rdword_of_val_mem; [|exact HFL].
apply (fsw_field E (mrestrict H mem) 24 (fe_F cx) fcs 0 64 0 64 56 8 (SOff 44 0) (fe_FL cx) Hr H24 Hin);
  [| exact HFL | cbn; lia].
rewrite fsw_SOff0. change 44%nat with (32 + 12)%nat. rewrite (HE 12%nat) by lia. reflexivity.
Qed.
(* len = -1, from the frame region's chunk at 32 *)
Lemma fe3_len_ok : forall E E' m b fcs z,
  region_ok tfibsegs E m (YP09.mkRegion (Some 24%nat) 0 64 0 64 fcs) -> bv_unsigned (ew E 24) = b ->
  In (YP09.mkChunk 32 (CVal 8 (SLit z))) fcs -> Z_to_bv 64 z = Z_to_bv 64 (-1) ->
  YP09.chunk_ok tfibsegs E' m b (fe_len_lit (-1)).
Proof.
intros E E' m b fcs z (_ & _ & _ & Hcs) Hb Hin Hz.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hb in Hck.
intros i Hi. destruct (Hck i Hi) as (bt & H1 & H2). exists bt. split; [|exact H2].
rewrite <- H1. cbn [cbyte fe_len_lit YP09.c_val YP09.c_off sv_denot]. rewrite Hz. reflexivity.
Qed.
Lemma fe3_m1 : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma fe3_rebuild : forall cx E ss ms ly3 S3 W3 md3 k r cs fcs xs,
  fe_base B cx -> fe_E cx E ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 W3 (unpoison [] (ms_mem ms)) md3 k ->
  ARU tfibsegs B ly3 S3 [] W3 (ms_mem ms) md3 ->
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ->
  st_ok tfibsegs E ss (restrict (w_H W3) ms) -> fe3_atoms_kept ss -> fe_regs_core cx E ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 24%nat) 0 64 0 64 fcs) ->
  In (YP09.mkChunk 56 (CVal 8 (SOff 44 0))) fcs ->
  nth_error (ss_mem ss) 2 = Some (fs_ret_s0_region (-88) 0 fe_sv_chunks) ->
  regions_wf (fe_regions cs) = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 56) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg (ms_regs ms) (fe_extra cx ++ xs)) (mrestrict (w_H W3) (ms_mem ms)) (fe_F cx)) cs ->
  st_ok tfibsegs (Ereg (ms_regs ms) (fe_extra cx ++ xs)) (fe_ss r cs)
    (restrict (w_H W3) (YK11.mkst (ms_regs ms) (Z_to_bv 64 r) (ms_mem ms) (YK11.seg_rom tfibsegs))).
Proof.
intros cx E ss ms ly3 S3 W3 md3 k r cs fcs xs Hbase HE HJ HARU Hab HS Hat Hcore H0 Hin56 H2 Hwf Hcin Hcs.
pose proof (fe3_geo cx k ly3 S3 W3 _ md3 Hbase HJ Hab)
  as (Hfr3 & EF & ET & EFa & EFl & Hal32 & H4096 & Hfc & Hfl & Hs1 & Hs3 & _ & _ & _).
pose proof (fe3_base_facts cx Hbase) as (Hal & Hsp & Htop & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (fe3_core_after cx E ss ms (w_H W3) xs HS Hat Hcore) as (_ & R8 & R24 & R18 & R25).
assert (Hr0 : region_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 24%nat) 0 64 0 64 fcs))
  by exact (fsw_region_nth E ss (restrict (w_H W3) ms) 0 _ HS H0).
assert (Hr2 : region_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (fs_ret_s0_region (-88) 0 fe_sv_chunks))
  by exact (fsw_region_nth E ss (restrict (w_H W3) ms) 2 _ HS H2).
destruct Hcore as (C8 & _ & _ & _ & C24 & _).
assert (U24 : bv_unsigned (ew E 24) = fe_F cx) by (rewrite C24; apply wz; lia).
assert (U8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite C8; apply wz; unfold LLVMF_STK in Hsp; lia).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
rewrite FSupoison.unpoison_nil in Hpres.
apply (fe_canon B cx ly3 S3 [] W3 (ms_mem ms) md3 (ms_regs ms) xs r cs HARU).
- rewrite Hfr3. left. reflexivity.
- exact EF.
- exact R8.
- exact R24.
- exact R18.
- exact R25.
- exact Hal.
- unfold LLVMF_STK in Hsp. lia.
- lia.
- intros a Ha. apply Hpres. unfold LLVMF_STK. lia.
- destruct Hr2 as (_ & _ & _ & Hcs2). cbn [fs_ret_s0_region YP09.r_base YP09.r_chunks base_val] in Hcs2.
  rewrite U8 in Hcs2. exact (fe3_sv_ok cx E _ _ HE (fe_E_Ereg cx (ms_regs ms) xs) Hcs2).
- exact (fe3_flag_ok cx E (w_H W3) (ms_mem ms) fcs HE Hr0 U24 Hin56 ltac:(lia)).
- exact Hwf.
- exact Hcin.
- exact Hcs.
Qed.

(* the write window of a run over the canonical regions: the own frame and its shadow (in_frames), the saved words
   (the stack window); awr_byte0's arms, for any journal-entry frames fr0 *)
Lemma fe3_awr : forall cx E cs ly3 S3 fr0,
  frame_addr ly3 0 (c_fpos cx) = fe_F cx ->
  bv_unsigned (ew E 24) = fe_F cx -> bv_unsigned (ew E 25) = fe_SF cx -> bv_unsigned (ew E 8) = fe_sp0 cx ->
  awr_ok tfibsegs B E (fe_regions cs) LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx))
    (ablocks B ly3 S3) ly3 [(0, c_fpos cx)] fr0.
Proof.
intros cx E cs ly3 S3 fr0 EFa U24 U25 U8. unfold fe_regions.
eapply awr_ok_cons_gen with (k := 24%nat) (b := fe_F cx); [reflexivity | exact U24 | |].
{ intros a Ha. cbn [fe_frame_region YP09.r_wlo YP09.r_whi] in Ha. left. right. right. right.
  exists 0, (c_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EFa.
  change (fs_frame_bytes 0) with 64. lia. }
eapply awr_ok_cons_gen with (k := 25%nat) (b := fe_SF cx); [reflexivity | exact U25 | |].
{ intros a Ha. cbn [fe_shadow_region YP09.r_wlo YP09.r_whi] in Ha. left. right. right. right.
  exists 0, (c_fpos cx). split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite EFa.
  change (fs_frame_bytes 0 / 8) with 8. change (shadow_addr (fe_F cx)) with (fe_SF cx). lia. }
eapply awr_ok_cons_stack_off with (n := 8%nat) (d := 0);
  [reflexivity | rewrite U8; lia | cbn; unfold LLVMF_STK; lia | cbn; lia | apply awr_ok_nil].
Qed.

(* the canonical register values as unsigned numbers *)
Lemma fe3_core_u : forall cx E, fe_base B cx -> fe_regs_core cx E ->
  4096 <= fe_F cx -> fe_F cx + 64 <= alloc_ceiling -> fe_SF cx + 8 <= kHighMemBeg -> 0 <= fe_SF cx ->
  bv_unsigned (ew E 8) = fe_sp0 cx /\ bv_unsigned (ew E 24) = fe_F cx /\ bv_unsigned (ew E 25) = fe_SF cx /\
  bv_unsigned (ew E 18) = fe_F cx.
Proof.
intros cx E Hbase (C8 & _ & _ & C18 & C24 & C25 & _) H1 H2 H3 H4.
pose proof (fe3_base_facts cx Hbase) as (_ & Hsp & Htop & H47 & _).
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
rewrite C8, C24, C25, C18. unfold kHighMemBeg in H3.
split; [apply wz; unfold LLVMF_STK in Hsp; lia|]. split; [apply wz; lia|]. split; apply wz; lia.
Qed.

(* ---- the head: from memchr's return (C1) through `beqz` / `sub` / the two stores to the `bltu` ---- *)
Lemma fe3_head_enter : forall POST cx E k ly3 S3 W3 ms3 md3 ss ms md,
  fe_from B FS_PSTAT_FP POST (fe_ss PC_s3mid [fe_len_lit (-1)]) INV_S3mid ->
  fe_base B cx -> fe_E cx E ->
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) -> st_nev S3 = st_nev (c_S cx) ->
  blocks_bytes S3 = blocks_bytes (c_S cx) ->
  fe_common cx k S3 W3 ms3 md3 0 -> fe_regs_core cx E -> ew E 20 = Z_to_bv 64 (c_p cx) ->
  ew E 22 = Z_to_bv 64 SHADOW_OFF -> fs_stat tfibsegs W3 (ms_mem ms3) (c_live cx) (c_cnt cx) ->
  frame_of E (fe_regions []) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 W3 (unpoison [] (ms_mem ms)) md k ->
  ARU tfibsegs B ly3 S3 [] W3 (ms_mem ms) md -> same_io md3 md ->
  st_ok tfibsegs E ss (restrict (w_H W3) ms) -> ss_resv ss = None -> ss_pc ss = PC_s3mid -> fe3_atoms_kept ss ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 24%nat) 0 64 0 64
    [YP09.mkChunk 32 (CVal 8 (SLit 18446744073709551615)); YP09.mkChunk 56 (CVal 8 (SOff 44 0))]) ->
  nth_error (ss_mem ss) 2 = Some (fs_ret_s0_region (-88) 0 fe_sv_chunks) ->
  nth_error (ss_mem ss) 1 = Some fe_shadow_region_z ->
  sr_get (ss_regs ss) 11%bv = SLit 3145728 -> sr_get (ss_regs ss) 20%bv = SOff 20 0 ->
  sr_get (ss_regs ss) 22%bv = SOff 22 0 ->
  sv_denot E (sr_get (ss_regs ss) 19%bv) = Z_to_bv 64 (fe_n cx) ->
  SRr tfibsegs W3 (mkCfg ms md) (POST cx).
Proof.
intros POST cx E k ly3 S3 W3 ms3 md3 ss ms md HM Hbase HE Hab Hnev Hbb Hcom Hcore E20 E22 Hstat HFr HJ HARU Hio
  HS Hrv Hpc Hat H0 H2 H1z R11 R20 R22 R19.
pose proof (fe3_geo cx k ly3 S3 W3 _ md Hbase HJ Hab)
  as (Hfr3 & EF & ET & EFa & EFl & Hal32 & H4096 & Hfc & Hfl & Hs1 & Hs3 & Hpst & Hpay & _).
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
destruct (fe3_core_u cx E Hbase Hcore H4096 Hfc Hs3 ltac:(unfold kLowMemEnd in Hs1; lia)) as (U8 & U24 & U25 & _).
assert (Hr0 : region_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 24%nat) 0 64 0 64
    [YP09.mkChunk 32 (CVal 8 (SLit 18446744073709551615)); YP09.mkChunk 56 (CVal 8 (SOff 44 0))]))
  by exact (fsw_region_nth E ss (restrict (w_H W3) ms) 0 _ HS H0).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ss ms HS Hrv), Hpc.
destruct Hcom as (Hk & Hio0 & Hpl & Hbbs).
apply (HM cx (Ereg (ms_regs ms) (fe_extra cx ++ [])) k ly3 S3 [] W3
  (YK11.mkst (ms_regs ms) (Z_to_bv 64 PC_s3mid) (ms_mem ms) (YK11.seg_rom tfibsegs)) md Hbase (fe_E_Ereg cx (ms_regs ms) [])
  HJ HARU).
- unfold INV_S3mid.
  change (ms_mem (YK11.mkst (ms_regs ms) (Z_to_bv 64 PC_s3mid) (ms_mem ms) (YK11.seg_rom tfibsegs))) with (ms_mem ms).
  split; [reflexivity|]. split; [exact Hab|]. split; [exact Hnev|]. split; [exact Hbb|].
  split.
  { split; [exact Hk|]. split; [exact (same_io_trans _ _ _ Hio0 Hio)|]. split; [|exact Hbbs].
    intros i Hi. destruct (Hpay i Hi) as (Hr & N1 & N2 & N3 & _).
    transitivity (aview tfibsegs (w_H W3) (ms_mem ms3) (c_p cx + i));
      [exact (fe3_aview_keep cx E [] (w_H W3) (ms_mem ms3) (ms_mem ms) (c_p cx + i) HFr U24 U25 U8 Hr N1 N2 N3)
      | exact (Hpl i Hi)]. }
  split; [exact (proj1 (fe3_core_after cx E ss ms (w_H W3) [] HS Hat Hcore))|].
  rewrite (ew_Ereg_nat (ms_regs ms) _ 11 11%bv eq_refl), (ew_Ereg_nat (ms_regs ms) _ 19 19%bv eq_refl),
    (ew_Ereg_nat (ms_regs ms) _ 20 20%bv eq_refl), (ew_Ereg_nat (ms_regs ms) _ 22 22%bv eq_refl).
  rewrite (st_ok_reg tfibsegs E ss (restrict (w_H W3) ms) 11%bv HS), R11.
  split; [reflexivity|].
  rewrite (st_ok_reg tfibsegs E ss (restrict (w_H W3) ms) 19%bv HS). split; [exact R19|].
  rewrite (fe3_reg_at E ss ms (w_H W3) 20%bv 20 HS R20), (fe3_reg_at E ss ms (w_H W3) 22%bv 22 HS R22).
  split; [exact E20|]. split; [exact E22|].
  split.
  { apply (fe3_stat_keep W3 (ms_mem ms3) (ms_mem ms)); [|exact Hstat].
    intros a Ha. pose proof (pstat_bounds a Ha) as Hb. destruct (Hpst a Ha) as (N1 & N2 & N3).
    apply (fe3_frame_keep E [] _ _ _ HFr); rewrite (wz a ltac:(lia)); [rewrite U24 | rewrite U25 | rewrite U8]; assumption. }
  exact (fe_lensh_of cx E ss (w_H W3) ms HS H1z U25).
- apply (fe3_rebuild cx E ss ms ly3 S3 W3 md k PC_s3mid [fe_len_lit (-1)]
    [YP09.mkChunk 32 (CVal 8 (SLit 18446744073709551615)); YP09.mkChunk 56 (CVal 8 (SOff 44 0))] []
    Hbase HE HJ HARU Hab HS Hat Hcore H0 ltac:(right; left; reflexivity) H2 (fe_regions_wf_len_lit (-1))).
  + constructor; [cbn; lia | constructor].
  + constructor; [|constructor].
    exact (fe3_len_ok E _ _ _ _ _ Hr0 U24 ltac:(left; reflexivity) fe3_m1).
Qed.

Ltac fe3_conc := vm_compute; repeat match goal with |- _ /\ _ => split | |- _ = _ => reflexivity end.

Lemma fe3_seg3_head : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss PC_s3mid [fe_len_lit (-1)]) INV_S3mid ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_memchr []) (INV_C1 B).
Proof.
intros POST HM cx E k ly3 S3 U3 W3 ms3 md3 Hbase HE HJ HARU HINV HS.
destruct HINV as (-> & Hab & Hnev & Hbb & Hcom & Hcore & E10 & E19 & E20 & E22 & Hstat).
pose proof (fe3_base_facts cx Hbase) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpn & Hlen & _).
pose proof (fe3_geo cx k ly3 S3 W3 _ md3 Hbase HJ Hab)
  as (Hfr3 & EF & ET & EFa & EFl & Hal32 & H4096 & Hfc & Hfl & Hs1 & Hs3 & Hpst & Hpay & Hblk).
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
destruct (fe3_core_u cx E Hbase Hcore H4096 Hfc Hs3 ltac:(unfold kLowMemEnd in Hs1; lia)) as (U8 & U24 & U25 & _).
assert (Hlenb : length (fe_bytes cx) = length (c_pl cx)) by (unfold fe_bytes; apply length_map).
eapply (SRr_sym_branch tfibsegs W3 E (fe_ss RA_memchr []) ms3 md3 (POST cx) BC_EQ (SOff 10 0) (SLit 0) HS);
  intros Hbr HS1.
- (* a0 = 0: the payload has no NUL; s3 keeps size *)
  assert (Ez : zfind 0 (fe_bytes cx) = None).
  { destruct (zfind 0 (fe_bytes cx)) as [j|] eqn:Ez; [|reflexivity]. exfalso.
    destruct (fe3_zfind_some 0 _ j Ez) as (Hj & _).
    assert (Hn : 0 < c_n cx) by lia.
    destruct (Hblk Hn) as (Hp4 & Hpr & _).
    unfold fe_memchr_res in E10. rewrite Ez in E10.
    cbn [branch_taken] in Hbr. rewrite fsw_SOff0, E10 in Hbr. cbn [sv_denot] in Hbr.
    rewrite bv_eqb_unsigned, !wz in Hbr by lia. apply Z.eqb_eq in Hbr. lia. }
  fsw_aj_runU entry_tbl_ok HS1 HJ HARU.
  + exact (fe3_awr cx E [] ly3 S3 _ EFa U24 U25 U8).
  + eapply (fe3_head_enter POST cx E k ly3 S3 W3 ms3 md3 _ _ _ HM Hbase HE Hab Hnev Hbb Hcom Hcore E20 E22 Hstat HFr
      HJ HARU (fe3_same_io_wvb _ _ _) HS1); [fe3_conc | fe3_conc | fe3_conc | fe3_conc | fe3_conc | fe3_conc | fe3_conc | fe3_conc | fe3_conc |].
    match goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
    rewrite fsw_SOff0, E19. unfold fe_n. rewrite Ez. reflexivity.
- (* a0 <> 0: the first NUL at j; s3 := a0 - s4 = j *)
  assert (Ez : exists j, zfind 0 (fe_bytes cx) = Some j).
  { destruct (zfind 0 (fe_bytes cx)) as [j|] eqn:Ez; [exists j; reflexivity|]. exfalso.
    unfold fe_memchr_res in E10. rewrite Ez in E10.
    cbn [branch_taken] in Hbr. rewrite fsw_SOff0, E10 in Hbr. vm_compute in Hbr. discriminate Hbr. }
  destruct Ez as (j & Ez).
  destruct (fe3_zfind_some 0 _ j Ez) as (Hj & _).
  assert (Hn : 0 < c_n cx) by lia.
  destruct (Hblk Hn) as (Hp4 & Hpr & _).
  fsw_aj_runU entry_tbl_ok HS1 HJ HARU.
  + exact (fe3_awr cx E [] ly3 S3 _ EFa U24 U25 U8).
  + eapply (fe3_head_enter POST cx E k ly3 S3 W3 ms3 md3 _ _ _ HM Hbase HE Hab Hnev Hbb Hcom Hcore E20 E22 Hstat HFr
      HJ HARU (fe3_same_io_wvb _ _ _) HS1); [fe3_conc | fe3_conc | fe3_conc | fe3_conc | fe3_conc | fe3_conc | fe3_conc | fe3_conc | fe3_conc |].
    match goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
    unfold fe_n. rewrite Ez. rewrite denot_lit_U. f_equal.
    rewrite U_SAlu, U_SMd, !U_SOff, U_SLit.
    unfold fe_memchr_res in E10. rewrite Ez in E10. rewrite E10, E20, !wz by lia.
    cbn [zalu_raw zmd_raw]. unfold zcanon, M64. rewrite !Z.add_0_r.
    rewrite (Z.mod_small (c_p cx + Z.of_nat j)) by lia. rewrite (Z.mod_small (c_p cx)) by lia.
    replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
    rewrite Zplus_mod_idemp_r.
    replace (c_p cx + Z.of_nat j + c_p cx * (2 ^ 64 - 1)) with (Z.of_nat j + c_p cx * 2 ^ 64) by ring.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* ---- the `n > 3 MiB` exit: the run reaches the epilogue (C9) ---- *)
Lemma fe3_epi_enter : forall POST cx E k ly3 S3 W3 ms3 md3 ss ms md,
  fe_from B FS_PSTAT_FP POST (fe_ss PC_epi []) (INV_C9 B) ->
  fe_base B cx -> fe_E cx E ->
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ->
  fe_common cx k S3 W3 ms3 md3 0 -> fe_regs_core cx E ->
  fs_stat tfibsegs W3 (ms_mem ms3) (c_live cx) (c_cnt cx) ->
  frame_of E (fe_regions [fe_len_lit (-1)]) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 W3 (unpoison [] (ms_mem ms)) md k ->
  ARU tfibsegs B ly3 S3 [] W3 (ms_mem ms) md -> same_io md3 md ->
  st_ok tfibsegs E ss (restrict (w_H W3) ms) -> ss_resv ss = None -> ss_pc ss = PC_epi -> fe3_atoms_kept ss ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 24%nat) 0 64 0 64
    [YP09.mkChunk 56 (CVal 8 (SOff 44 0)); YP09.mkChunk 32 (CVal 8 (SLit (-1)))]) ->
  nth_error (ss_mem ss) 2 = Some (fs_ret_s0_region (-88) 0 fe_sv_chunks) ->
  SRr tfibsegs W3 (mkCfg ms md) (POST cx).
Proof.
intros POST cx E k ly3 S3 W3 ms3 md3 ss ms md H9 Hbase HE Hab Hcom Hcore Hstat HFr HJ HARU Hio
  HS Hrv Hpc Hat H0 H2.
pose proof (fe3_geo cx k ly3 S3 W3 _ md Hbase HJ Hab)
  as (Hfr3 & EF & ET & EFa & EFl & Hal32 & H4096 & Hfc & Hfl & Hs1 & Hs3 & Hpst & Hpay & _).
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
destruct (fe3_core_u cx E Hbase Hcore H4096 Hfc Hs3 ltac:(unfold kLowMemEnd in Hs1; lia)) as (U8 & U24 & U25 & _).
pose proof (fe3_base_facts cx Hbase) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hc0 & Hcm).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ss ms HS Hrv), Hpc.
destruct Hcom as (Hk & Hio0 & Hpl & Hbbs).
apply (H9 cx (Ereg (ms_regs ms) (fe_extra cx ++ [])) k ly3 S3 [] W3
  (YK11.mkst (ms_regs ms) (Z_to_bv 64 PC_epi) (ms_mem ms) (YK11.seg_rom tfibsegs)) md Hbase (fe_E_Ereg cx (ms_regs ms) [])
  HJ HARU).
- unfold INV_C9.
  change (ms_mem (YK11.mkst (ms_regs ms) (Z_to_bv 64 PC_epi) (ms_mem ms) (YK11.seg_rom tfibsegs))) with (ms_mem ms).
  split; [reflexivity|]. split; [rewrite Hab; reflexivity|].
  split.
  { assert (HX : 0 <= EV_check_no_overread + 1 + EV_preset_base64_decode + EV_check_as_written + EV_check_round_trip + 2)
      by (vm_compute; discriminate).
    split; [lia|].
    split; [exact (same_io_trans _ _ _ Hio0 Hio)|]. split; [|exact Hbbs].
    intros i Hi. destruct (Hpay i Hi) as (Hr & N1 & N2 & N3 & _).
    transitivity (aview tfibsegs (w_H W3) (ms_mem ms3) (c_p cx + i));
      [exact (fe3_aview_keep cx E _ (w_H W3) (ms_mem ms3) (ms_mem ms) (c_p cx + i) HFr U24 U25 U8 Hr N1 N2 N3)
      | exact (Hpl i Hi)]. }
  split; [exact (proj1 (fe3_core_after cx E ss ms (w_H W3) [] HS Hat Hcore))|].
  assert (HX : 0 <= FE_CNT_MAX) by (vm_compute; discriminate).
  exists (c_cnt cx). split; [|lia].
  apply (fe3_stat_keep W3 (ms_mem ms3) (ms_mem ms)); [|exact Hstat].
  intros a Ha. pose proof (pstat_bounds a Ha) as Hb. destruct (Hpst a Ha) as (N1 & N2 & N3).
  apply (fe3_frame_keep E _ _ _ _ HFr); rewrite (wz a ltac:(lia)); [rewrite U24 | rewrite U25 | rewrite U8]; assumption.
- exact (fe3_rebuild cx E ss ms ly3 S3 W3 md k PC_epi []
    [YP09.mkChunk 56 (CVal 8 (SOff 44 0)); YP09.mkChunk 32 (CVal 8 (SLit (-1)))] []
    Hbase HE HJ HARU Hab HS Hat Hcore H0 ltac:(left; reflexivity) H2 fe_regions_wf_nil (Forall_nil _) (Forall_nil _)).
Qed.

(* ---- the program call: check_no_overread(data, n) at 0x81048 ---- *)
Lemma fe3_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.

(* the relro / rom view at any state of the walk: the entry's (tfib_lib_pre_x), kept by the journal's image clause
   (rodata is image, not a static of FS_PSTAT_FP, and the footprint is closed) *)
Lemma fe3_arodata : forall cx ly3 S3 W3 mem3 md3 k,
  fe_base B cx ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 W3 mem3 md3 k ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W3) mem3).
Proof.
intros cx ly3 S3 W3 mem3 md3 k Hbase HJ a Ha Ho He.
pose proof (fe3_base_facts cx Hbase) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Himg : in_img tfibsegs a).
{ destruct Ha as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr]|].
  apply (seg_covers_img FS_RLO (FS_RHI - FS_RLO)); [vm_compute; reflexivity | lia]. }
assert (Hnfp : ~ inFP FS_PSTAT_FP a).
{ intros Hf. pose proof (pstat_bounds a Hf) as Hb.
  destruct Ha as [(sg & Hsg & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; lia].
  assert (Hall : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0xa1000)
     || (0x5fd000 <=? Z.of_N (seg_base s))) tfibsegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall sg Hsg). rewrite Hw in Hall. cbn [orb] in Hall.
  apply orb_prop in Hall as [H1|H1]; apply Z.leb_le in H1; lia. }
rewrite (F3 a Himg Ho He Hnfp (fp_spares_closed FS_PSTAT_FP a fe3_closed)).
exact (Hro a Ha Ho He).
Qed.

(* the text check_no_overread reads: the payload's first n bytes, NUL-free, in the payload block (or empty at
   A_EMPTY) *)
Lemma fe3_src : forall cx ly3 S3 W3 mem md3 k,
  fe_base B cx ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 W3 (unpoison [] mem) md3 k ->
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ->
  (forall i, 0 <= i < c_n cx ->
     aview tfibsegs (w_H W3) mem (c_p cx + i) = aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)) ->
  src_rd tfibsegs W3 mem (c_p cx) (fe_tb cx) /\
  (0 < Z.of_nat (length (fe_tb cx)) -> exists b m, In (b, m) (ablocks B ly3 S3) /\ b <= c_p cx /\
     c_p cx + Z.of_nat (length (fe_tb cx)) <= b + m).
Proof.
intros cx ly3 S3 W3 mem md3 k Hbase HJ Hab Hpl.
pose proof (fe3_base_facts cx Hbase) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpn & Hlen & Hgarr & _).
destruct (fe3_n_facts cx Hlen) as (Hn0 & Hlt & _ & Hnth).
pose proof (fe3_geo cx k ly3 S3 W3 _ md3 Hbase HJ Hab) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
pose proof HJ as (HAR & _). rewrite FSupoison.unpoison_nil in HAR.
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
assert (Hlb : length (fe_bytes cx) = length (c_pl cx)) by (unfold fe_bytes; apply length_map).
destruct Hpn as [(Hn & Hp) | (Hn & Hpin)].
- assert (Hl0 : length (fe_tb cx) = 0%nat) by lia.
  unfold src_rd. rewrite Hl0. cbn [Z.of_nat].
  split; [|lia].
  split; [intros j Hj; rewrite Hl0 in Hj; lia|].
  rewrite Hp. unfold A_EMPTY. split; [lia|]. split; [lia|]. split; [left; unfold kLowMemEnd; lia|].
  split; [apply range_addressable_nil; lia | lia].
- destruct (Hblk (proj1 Hn)) as (Hp4 & Hroom & Hpin3).
  pose proof (AR_laws_ok tfibsegs B) as LAWS.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem md3 _ _ HAR Hpin3) as (_ & _ & _ & Hpapp & _).
  destruct (al_shadow _ _ LAWS ly3 S3 W3 mem md3 _ _ HAR Hpin3) as (_ & Hhull).
  assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  split; [|intros _; exists (c_p cx), (c_n cx); split; [exact Hpin3|]; lia].
  unfold src_rd. split.
  + unfold zbytes_at. intros j Hj. rewrite (Hnth j Hj).
    assert (Hj' : (j < length (fe_bytes cx))%nat) by lia.
    destruct (Hgarr j Hj') as (Hv & Hb). split; [|exact Hb].
    apply (val_mem_kept tfibsegs (w_H (c_W cx)) (w_H W3) (c_mem cx) mem _ 1 _); [|exact Hv].
    intros k0 Hk0. replace (c_p cx + Z.of_nat j + k0) with (c_p cx + Z.of_nat j) by lia. apply Hpl. lia.
  + split; [lia|]. split; [lia|]. split.
    * unfold amem_range. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hpapp. rewrite Hrq in Hpapp.
      unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
    * split; [exact (range_addressable_of_block tfibsegs B LAWS ly3 S3 W3 mem md3 (c_p cx) (c_n cx) (c_p cx)
                (Z.of_nat (length (fe_tb cx))) HAR Hpin3 ltac:(lia) ltac:(rewrite Hrq; lia))|].
      intros Hl. apply (shadow_hull_vis_sub _ (c_p cx) (req_size (c_n cx))); [exact Hhull | lia | rewrite Hrq; lia | exact Hl].
Qed.

(* the saved words lie in [sp0 - 88, sp0) *)
Lemma fe3_sv_range : forall c, In c fe_sv_chunks -> -88 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 0.
Proof.
intros c Hc. unfold fe_sv_chunks in Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
cbn [YP09.c_off YP09.c_len YP09.c_val cv_len]. cbn. lia.
Qed.
Lemma fe3_chunks_keep : forall E (H H' : word -> bool) m m' base cs,
  (forall c, In c cs -> forall i, 0 <= i < YP09.c_len c ->
     aview tfibsegs H' m' (base + YP09.c_off c + i) = aview tfibsegs H m (base + YP09.c_off c + i)) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict H m) base) cs ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict H' m') base) cs.
Proof.
intros E H H' m m' base cs Hk Hcs. apply Forall_forall. intros c Hc.
apply (chunk_ok_mbyte E (mrestrict H m)); [|exact (proj1 (Forall_forall _ _) Hcs c Hc)].
intros i Hi. apply mbyte_of_aview. exact (Hk c Hc i Hi).
Qed.

(* the callee's chain: s0 = the entry sp; its frame record (saved ra = RA_LLVMF, saved s0) pushed on the entry's
   empty chain, or no chain when the entry sp is within 16 of ly_top *)
Lemma fe3_chain : forall cx E ss ms ly3 S3 W3 md k,
  fe_base B cx -> fe_E cx E ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 W3 (unpoison [] (ms_mem ms)) md k ->
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ->
  st_ok tfibsegs E ss (restrict (w_H W3) ms) ->
  nth_error (ss_mem ss) 2 = Some (fs_ret_s0_region (-88) 0 fe_sv_chunks) ->
  bv_unsigned (ew E 8) = fe_sp0 cx ->
  YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (fe_sp0 cx) -> YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 RA_cno ->
  spZ (ms_regs ms) + 16 <= fe_sp0 cx ->
  exists ch, achain ly3 (aview tfibsegs (w_H W3) (unpoison [] (ms_mem ms))) (spZ (ms_regs ms)) (s0Z (ms_regs ms)) ch.
Proof.
intros cx E ss ms ly3 S3 W3 md k Hbase HE HJ Hab HS H2 U8 R8 R1 Hsp.
pose proof (fe3_base_facts cx Hbase) as (Hal & Hsp0 & Htop & H47 & Hra & _ & _ & Hch & _).
pose proof (fe3_geo cx k ly3 S3 W3 _ md Hbase HJ Hab) as (_ & _ & ET & _).
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
assert (Hs0 : s0Z (ms_regs ms) = fe_sp0 cx) by (unfold s0Z; rewrite R8; apply wz; unfold LLVMF_STK in Hsp0; lia).
rewrite Hs0.
destruct (Z_lt_le_dec (fe_sp0 cx) (ly_top ly3 - 16)) as [Hlt | Hge].
- exists [(fe_sp0 cx, RA_LLVMF, s0Z (c_regs cx))].
  assert (Hr2 : region_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (fs_ret_s0_region (-88) 0 fe_sv_chunks))
    by exact (fsw_region_nth E ss (restrict (w_H W3) ms) 2 _ HS H2).
  apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ET).
  apply (achain_push (c_ly cx) (aview tfibsegs (w_H (c_W cx)) (c_mem cx)) _ (fe_sp0 cx) (s0Z (c_regs cx)) RA_LLVMF []
    _ Hch).
  + lia.
  + pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
    intros a Ha. apply F1; [unfold LLVMF_STK in Hsp0; lia | lia].
  + rewrite FSupoison.unpoison_nil. apply ACem.rdword_of_val_mem; [|unfold RA_LLVMF; lia].
    replace (fe_sp0 cx - 8) with (fe_sp0 cx + -8) by lia.
    apply (fsw_field E _ 8 (fe_sp0 cx) fe_sv_chunks (-88) 0 (-88) 0 (-8) 8 (SOff 33 0) RA_LLVMF Hr2 U8);
      [cbn; left; reflexivity | | unfold RA_LLVMF; lia | cbn; lia].
    rewrite fsw_SOff0. change 33%nat with (32 + 1)%nat. rewrite (HE 1%nat) by lia. cbn [nth fe_extra map app fe_saved_regs].
    rewrite <- Hra. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned.
  + rewrite FSupoison.unpoison_nil. apply ACem.rdword_of_val_mem; [|unfold s0Z; apply u64_range].
    replace (fe_sp0 cx - 16) with (fe_sp0 cx + -16) by lia.
    apply (fsw_field E _ 8 (fe_sp0 cx) fe_sv_chunks (-88) 0 (-88) 0 (-16) 8 (SOff 34 0) (s0Z (c_regs cx)) Hr2 U8);
      [cbn; right; left; reflexivity | | unfold s0Z; apply u64_range | cbn; lia].
    rewrite fsw_SOff0. change 34%nat with (32 + 2)%nat. rewrite (HE 2%nat) by lia. cbn [nth fe_extra map app fe_saved_regs].
    unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned.
  + unfold RA_LLVMF. lia.
  + unfold LLVMF_STK in Hsp0. lia.
  + rewrite Zmod_divides in Hal by lia. destruct Hal as (q & Hq). rewrite Hq. rewrite Z.mul_comm.
    replace (q * 16) with ((2 * q) * 8) by ring. apply Z_mod_mult.
  + rewrite <- ET. exact Hlt.
  + exact Hsp.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.

Ltac fe3_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in
    change (bv_unsigned q) with z end; lia.

(* the call at 0x81048 and the return to 0x8104c (C2) *)
Lemma fe3_call : forall POST cx E k ly3 S3 W3 ms3 md3 ss ms md,
  fe_from B FS_PSTAT_FP POST (fe_ss RA_cno [fe_len_lit (-1)]) (INV_C2 B) ->
  fe_base B cx -> fe_E cx E ->
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) -> st_nev S3 = st_nev (c_S cx) ->
  blocks_bytes S3 = blocks_bytes (c_S cx) ->
  fe_common cx k S3 W3 ms3 md3 0 -> fe_regs_core cx E ->
  ew E 19 = Z_to_bv 64 (fe_n cx) -> ew E 20 = Z_to_bv 64 (c_p cx) -> ew E 22 = Z_to_bv 64 SHADOW_OFF ->
  fe_n cx <= 3 * 2 ^ 20 ->
  fs_stat tfibsegs W3 (ms_mem ms3) (c_live cx) (c_cnt cx) ->
  frame_of E (fe_regions [fe_len_lit (-1)]) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 W3 (unpoison [] (ms_mem ms)) md k ->
  ARU tfibsegs B ly3 S3 [] W3 (ms_mem ms) md -> same_io md3 md ->
  st_ok tfibsegs E ss (restrict (w_H W3) ms) -> ss_resv ss = None -> ss_pc ss = A_check_no_overread ->
  fe3_atoms_kept ss ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 24%nat) 0 64 0 64
    [YP09.mkChunk 56 (CVal 8 (SOff 44 0)); YP09.mkChunk 32 (CVal 8 (SLit (-1)))]) ->
  nth_error (ss_mem ss) 2 = Some (fs_ret_s0_region (-88) 0 fe_sv_chunks) ->
  nth_error (ss_mem ss) 1 = Some fe_shadow_region_z ->
  sr_get (ss_regs ss) 1%bv = SLit RA_cno -> sr_get (ss_regs ss) 10%bv = SOff 20 0 ->
  sr_get (ss_regs ss) 11%bv = SOff 19 0 -> sr_get (ss_regs ss) 19%bv = SOff 19 0 ->
  sr_get (ss_regs ss) 20%bv = SOff 20 0 -> sr_get (ss_regs ss) 22%bv = SOff 22 0 ->
  SRr tfibsegs W3 (mkCfg ms md) (POST cx).
Proof.
intros POST cx E k ly3 S3 W3 ms3 md3 ss ms md H2 Hbase HE Hab Hnev Hbb Hcom Hcore E19 E20 E22 Hsmall Hstat HFr HJ
  HARU Hio HS Hrv Hpc Hat H0 Hr2 H1z R1 R10 R11 R19 R20 R22.
pose proof (fe3_geo cx k ly3 S3 W3 _ md Hbase HJ Hab)
  as (Hfr3 & EF & ET & EFa & EFl & Hal32 & H4096 & Hfc & Hfl & Hs1 & Hs3 & Hpst & Hpay & Hblk).
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
pose proof (fe3_base_facts cx Hbase)
  as (Hal & Hsp0 & Htop & H47 & Hra & Hgp & Htp & Hch & Hfr & Hnev0 & Hbb0 & Hpn & Hlen & Hgarr & Hro & Hc0 & Hcm).
destruct (fe3_core_u cx E Hbase Hcore H4096 Hfc Hs3 ltac:(unfold kLowMemEnd in Hs1; lia)) as (U8 & U24 & U25 & _).
destruct (fe3_n_facts cx Hlen) as (Hn0 & Hlt & Hnz & _).
destruct Hcom as (Hk & Hio0 & Hpl & Hbbs).
pose proof Hcore as (C8 & C9 & C2 & C18 & C24 & C25 & C3 & C4 & C26 & C27).
destruct Hat as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q24 & Q25 & Q26 & Q27).
unfold LLVMF_STK in Hsp0.
(* the registers at the call *)
assert (RR : forall (r : bv 5) n, sr_get (ss_regs ss) r = SOff n 0 -> YK11.getr (ms_regs ms) r = ew E n)
  by (intros r n Hr; exact (fe3_reg_at E ss ms (w_H W3) r n HS Hr)).
assert (Rsp : YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 (fe_sp1 cx)) by (rewrite (RR _ _ Q2); exact C2).
assert (R1v : YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 RA_cno)
  by (rewrite (st_ok_reg tfibsegs E ss (restrict (w_H W3) ms) 1%bv HS), R1; reflexivity).
assert (R10v : YK11.getr (ms_regs ms) 10%bv = Z_to_bv 64 (c_p cx)) by (rewrite (RR _ _ R10); exact E20).
assert (R11v : YK11.getr (ms_regs ms) 11%bv = Z_to_bv 64 (fe_n cx)) by (rewrite (RR _ _ R11); exact E19).
assert (R8v : YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (fe_sp0 cx)) by (rewrite (RR _ _ Q8); exact C8).
assert (R3v : YK11.getr (ms_regs ms) 3%bv = w64 (as_gp B)) by (rewrite (RR _ _ Q3), C3; exact Hgp).
assert (R4v : YK11.getr (ms_regs ms) 4%bv = w64 (as_tp B)) by (rewrite (RR _ _ Q4), C4; exact Htp).
(* the re-aligned sp *)
pose proof (fsw_realign_facts (fe_sp0 cx - 96) ltac:(lia) ltac:(rewrite Zminus_mod, Hal; reflexivity)) as (Hq1 & Hq2 & Hq3).
change (32 * ((fe_sp0 cx - 96) / 32)) with (fe_sp1 cx) in Hq1, Hq2, Hq3.
assert (Usp : spZ (ms_regs ms) = fe_sp1 cx) by (unfold spZ; rewrite Rsp; apply wz; lia).
(* the payload and the statics at the call *)
assert (Hpl' : forall i, 0 <= i < c_n cx ->
  aview tfibsegs (w_H W3) (ms_mem ms) (c_p cx + i) = aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)).
{ intros i Hi. destruct (Hpay i Hi) as (Hr & N1 & N2 & N3 & _).
  transitivity (aview tfibsegs (w_H W3) (ms_mem ms3) (c_p cx + i));
    [exact (fe3_aview_keep cx E _ (w_H W3) (ms_mem ms3) (ms_mem ms) (c_p cx + i) HFr U24 U25 U8 Hr N1 N2 N3)
    | exact (Hpl i Hi)]. }
assert (Hstat' : fs_stat tfibsegs W3 (ms_mem ms) (c_live cx) (c_cnt cx)).
{ apply (fe3_stat_keep W3 (ms_mem ms3) (ms_mem ms)); [|exact Hstat].
  intros a Ha. pose proof (pstat_bounds a Ha) as Hb. destruct (Hpst a Ha) as (N1 & N2 & N3).
  apply (fe3_frame_keep E _ _ _ _ HFr); rewrite (wz a ltac:(lia)); [rewrite U24 | rewrite U25 | rewrite U8]; assumption. }
destruct Hstat' as (peak & Hglob).
(* the callee's chain and its pre *)
destruct (fe3_chain cx E ss ms ly3 S3 W3 md k Hbase HE HJ Hab HS Hr2 U8 R8v R1v ltac:(rewrite Usp; lia))
  as (ch & Hach).
(* check_no_overread's stack bound over the definitions, not its value: afn_pre_at's `0 <= STK1` and
   `STK1 - o <= LLVMF_STK` at o = fe_sp1 - fe_sp0 >= -127 *)
assert (HSTK : 0 <= STK_check_no_overread /\ STK_check_no_overread + 127 <= LLVMF_STK)
  by (split; apply Z.leb_le; vm_compute; reflexivity).
assert (Hfpre : fpreU tfibsegs B STK_check_no_overread ly3 S3 [] W3 (ms_regs ms) (ms_mem ms) md ch).
{ pose proof HARU as (_ & OK & PO).
  split; [split; [|split; [exact OK | exact PO]]|].
  - apply (afn_pre_at tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(0, c_fpos cx)] ly3 S3 W3 (unpoison [] (ms_mem ms)) md k (ms_regs ms) STK_check_no_overread
      (fe_sp1 cx - fe_sp0 cx) ch HJ).
    + rewrite Usp. ring.
    + rewrite Zminus_mod, Hq3, Hal. reflexivity.
    + lia.
    + lia.
    + unfold LLVMF_STK in *. lia.
    + rewrite R1v. vm_compute. reflexivity.
    + unfold raZ. rewrite R1v. rewrite wz; unfold RA_cno; lia.
    + exact R3v.
    + exact R4v.
    + exact Hach.
  - pose proof (fe3_arodata cx ly3 S3 W3 _ md k Hbase HJ) as Hro'. rewrite FSupoison.unpoison_nil in Hro'. exact Hro'. }
destruct (fe3_src cx ly3 S3 W3 (ms_mem ms) md k Hbase HJ Hab Hpl') as (Hsrc & Hblkd).
assert (HX : 3 <= FS_CNT_LIB) by (vm_compute; discriminate).
assert (HEV : EV_check_no_overread <= EV_LIB) by (vm_compute; discriminate).
assert (HLV : LIVE_check_no_overread <= ACfn.LIVE_LIB) by (vm_compute; discriminate).
pose proof (en_no_overread ly3 S3 [] W3 (ms_regs ms) (ms_mem ms) md ch (c_p cx) (fe_tb cx) (c_live cx) peak (c_cnt cx)
  SIZE_MAXZ Hfpre
  ltac:(intros r Hr; destruct Hr)
  ltac:(rewrite Hfr3; vm_compute; discriminate)
  ltac:(rewrite Usp, ET; lia)
  R10v
  ltac:(rewrite Hlt; exact R11v)
  Hsrc Hnz Hblkd
  ltac:(rewrite Hlt; unfold PRESET_FILE_MAX_BYTES; lia)
  Hglob
  ltac:(unfold quiet; split; [reflexivity|]; split; [exact Hc0 | lia])
  ltac:(pose proof Hbase as (_ & _ & _ & _ & Hlv); unfold ACfn.LIVE_LIB in Hlv;
        unfold FSH_Fn_writer.dec_size; rewrite Hlt; Z.div_mod_to_equations; lia)
  ltac:(rewrite Hnev; lia)
  ltac:(rewrite Hbb; lia)) as Hcall.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ss ms HS Hrv), Hpc.
change (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 A_check_no_overread) (ms_mem ms) (YK11.seg_rom tfibsegs)) md)
  with (cfg_at tfibsegs A_check_no_overread (ms_regs ms) (ms_mem ms) md).
apply (SRr_bind tfibsegs W3 _ _ _ Hcall).
intros W' c' Hle (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP & Hab' & peak' & Hpk & Hglob').
rewrite R1v.
(* the callee's journal composed onto the walk's *)
pose proof (fsw_ajournal_sub4 B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(0, c_fpos cx)] ly3 S3 W3 (unpoison [] (ms_mem ms)) md k STK_check_no_overread (spZ (ms_regs ms)) FS_PSTAT_FP []
  ly' S' W' (unpoison [] mem') md' EV_check_no_overread HJ HJc
  ltac:(rewrite Usp; unfold LLVMF_STK in *; lia) ltac:(rewrite Usp; lia)
  ltac:(intros a Ha; right; right; left; split; [exact Ha | apply fs_rw3_img, pstat_bounds, Ha])) as HJ2.
cbn [app] in HJ2.
assert (HARU2 : ARU tfibsegs B ly' S' [] W' mem' md') by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
assert (Hab2 : ablocks B ly' S' = ablocks B (c_ly cx) (c_S cx)) by (rewrite Hab'; exact Hab).
pose proof (fe3_geo cx (k + EV_check_no_overread) ly' S' W' _ md' Hbase HJ2 Hab2) as (Hfr3' & EF' & _).
(* the registers after the call *)
assert (HPr : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs' r = YK11.getr (ms_regs ms) r)
  by (intros r Hr; exact (fsw_pres _ _ r HP Hr)).
assert (R8' : YK11.getr regs' 8%bv = Z_to_bv 64 (fe_sp0 cx)) by (rewrite (HPr 8%bv ltac:(fe3_cs)); exact R8v).
assert (R9' : YK11.getr regs' 9%bv = Z_to_bv 64 (fe_sp1 cx)) by (rewrite (HPr 9%bv ltac:(fe3_cs)), (RR _ _ Q9); exact C9).
assert (R2' : YK11.getr regs' 2%bv = Z_to_bv 64 (fe_sp1 cx)) by (rewrite (HPr 2%bv ltac:(fe3_cs)); exact Rsp).
assert (R18' : YK11.getr regs' 18%bv = Z_to_bv 64 (fe_F cx)) by (rewrite (HPr 18%bv ltac:(fe3_cs)), (RR _ _ Q18); exact C18).
assert (R24' : YK11.getr regs' 24%bv = Z_to_bv 64 (fe_F cx)) by (rewrite (HPr 24%bv ltac:(fe3_cs)), (RR _ _ Q24); exact C24).
assert (R25' : YK11.getr regs' 25%bv = Z_to_bv 64 (fe_SF cx)) by (rewrite (HPr 25%bv ltac:(fe3_cs)), (RR _ _ Q25); exact C25).
(* what the callee's journal keeps: the saved words (above its stack window) and the own frame (frames clause) *)
pose proof HJc as (_ & _ & _ & _ & Hstep & _ & _ & _ & G1 & G2 & _ & G4 & _).
rewrite !FSupoison.unpoison_nil in G1, G2, G4.
assert (Kstack : forall a, fe_sp0 cx - 88 <= a < fe_sp0 cx ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W3) (ms_mem ms) a)
  by (intros a Ha; apply G1; [lia | rewrite Usp; lia]).
assert (Hin3 : In (0, c_fpos cx) (frames S3)) by (rewrite Hfr3; left; reflexivity).
assert (Kframe : forall a, fe_F cx <= a < fe_F cx + 64 ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W3) (ms_mem ms) a).
{ intros a Ha. apply (G4 0 (c_fpos cx) a Hin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 0) with 64. lia.
  - intros Hf. destruct (Hpst a Hf) as (N1 & _). exact (N1 Ha). }
(* `len`'s shadow byte: the frames clause keeps the live frame's shadow *)
assert (Hz' : fe_lensh cx W' mem').
{ unfold fe_lensh. rewrite (G4 0 (c_fpos cx) (fe_SF cx + 4) Hin3).
  - exact (fe_lensh_of cx E ss (w_H W3) ms HS H1z U25).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 0 / 8) with 8. unfold fe_SF. lia.
  - exact (fe_lensh_npstat cx ltac:(lia)). }
assert (Hr0 : region_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 24%nat) 0 64 0 64
    [YP09.mkChunk 56 (CVal 8 (SOff 44 0)); YP09.mkChunk 32 (CVal 8 (SLit (-1)))]))
  by exact (fsw_region_nth E ss (restrict (w_H W3) ms) 0 _ HS H0).
assert (Hr2r : region_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (fs_ret_s0_region (-88) 0 fe_sv_chunks))
  by exact (fsw_region_nth E ss (restrict (w_H W3) ms) 2 _ HS Hr2).
assert (Hflag' : rdword (aview tfibsegs (w_H W') mem') (fe_F cx + 56) = Some (fe_FL cx)).
{ rewrite (rdword_ext (aview tfibsegs (w_H W3) (ms_mem ms)) (aview tfibsegs (w_H W') mem'));
    [| intros k0 Hk0; apply Kframe; lia].
  exact (fe3_flag_ok cx E (w_H W3) (ms_mem ms) _ HE Hr0 U24 ltac:(left; reflexivity) ltac:(lia)). }
assert (Hsv' : Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fe_extra cx ++ [])) (mrestrict (w_H W') mem') (fe_sp0 cx))
  fe_sv_chunks).
{ destruct Hr2r as (_ & _ & _ & Hcs2). cbn [fs_ret_s0_region YP09.r_base YP09.r_chunks base_val] in Hcs2.
  rewrite U8 in Hcs2.
  apply (fe3_sv_ok cx E _ _ HE (fe_E_Ereg cx regs' [])).
  apply (fe3_chunks_keep E (w_H W3) (w_H W') (ms_mem ms) mem' (fe_sp0 cx) fe_sv_chunks); [|exact Hcs2].
  intros c Hc i Hi. pose proof (fe3_sv_range c Hc) as Hcr. apply Kstack. lia. }
assert (Hlen' : Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fe_extra cx ++ [])) (mrestrict (w_H W') mem') (fe_F cx))
  [fe_len_lit (-1)]).
{ apply (fe3_chunks_keep _ (w_H W3) (w_H W') (ms_mem ms) mem' (fe_F cx) [fe_len_lit (-1)]).
  - intros c Hc i Hi. destruct Hc as [<-|[]]. cbn [fe_len_lit YP09.c_off YP09.c_len YP09.c_val cv_len] in Hi |- *.
    apply Kframe. cbn in Hi. lia.
  - constructor; [|constructor]. exact (fe3_len_ok E _ _ _ _ (-1) Hr0 U24 ltac:(right; left; reflexivity) eq_refl). }
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
rewrite FSupoison.unpoison_nil in Hpres2.
assert (HS2 := fe_canon B cx ly' S' [] W' mem' md' regs' [] RA_cno [fe_len_lit (-1)] HARU2
  ltac:(rewrite Hfr3'; left; reflexivity) EF' R8' R24' R18' R25' Hal ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; apply Hpres2; unfold LLVMF_STK; lia) Hsv' Hflag' (fe_regions_wf_len_lit (-1))
  ltac:(constructor; [cbn; lia | constructor]) Hlen').
apply (H2 cx (Ereg regs' (fe_extra cx ++ [])) (k + EV_check_no_overread) ly' S' [] W'
  (YK11.mkst regs' (Z_to_bv 64 RA_cno) mem' (YK11.seg_rom tfibsegs)) md' Hbase (fe_E_Ereg cx regs' []) HJ2 HARU2);
  [|exact HS2].
unfold INV_C2.
change (ms_mem (YK11.mkst regs' (Z_to_bv 64 RA_cno) mem' (YK11.seg_rom tfibsegs))) with mem'.
assert (HEV12 : EV_check_no_overread = 12) by reflexivity.
split; [reflexivity|]. split; [exact Hab2|].
split.
{ split; [lia|]. split.
  { apply (same_io_trans _ _ _ Hio0). apply (same_io_trans _ _ _ Hio).
    exact (aos_step_closed_same_io _ _ _ fe3_closed Hstep). }
  split.
  - intros i Hi. destruct (Hpay i Hi) as (_ & _ & _ & _ & Hnfp).
    destruct (Hblk ltac:(lia)) as (_ & _ & Hpin3).
    assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
    transitivity (aview tfibsegs (w_H W3) (ms_mem ms) (c_p cx + i));
      [exact (G2 (c_p cx) (c_n cx) i Hpin3 ltac:(rewrite Hab'; exact Hpin3) ltac:(rewrite Hrq; lia) Hnfp)
      | exact (Hpl' i Hi)].
  - rewrite (blocks_bytes_bsum B ly' S'), Hab2, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)). lia. }
split.
{ apply fe3_core_of_regs; try assumption.
  - rewrite (HPr 3%bv ltac:(fe3_cs)), (RR _ _ Q3). exact C3.
  - rewrite (HPr 4%bv ltac:(fe3_cs)), (RR _ _ Q4). exact C4.
  - rewrite (HPr 26%bv ltac:(fe3_cs)), (RR _ _ Q26). exact C26.
  - rewrite (HPr 27%bv ltac:(fe3_cs)), (RR _ _ Q27). exact C27. }
split; [exact Hsmall|].
rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), (ew_Ereg_nat regs' _ 20 20%bv eq_refl),
  (ew_Ereg_nat regs' _ 22 22%bv eq_refl).
rewrite (HPr 19%bv ltac:(fe3_cs)), (HPr 20%bv ltac:(fe3_cs)), (HPr 22%bv ltac:(fe3_cs)), (RR _ _ R19), (RR _ _ R20),
  (RR _ _ R22).
split; [exact E19|]. split; [exact E20|]. split; [exact E22|].
split; [exists peak'; exact Hglob' | exact Hz'].
Qed.

(* ---- the tail: the `bltu` split at 0x8103c ---- *)
Lemma fe3_seg3_tail : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss PC_epi []) (INV_C9 B) ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_cno [fe_len_lit (-1)]) (INV_C2 B) ->
  fe_from B FS_PSTAT_FP POST (fe_ss PC_s3mid [fe_len_lit (-1)]) INV_S3mid.
Proof.
intros POST H9 H2 cx E k ly3 S3 U3 W3 ms3 md3 Hbase HE HJ HARU HINV HS.
destruct HINV as (-> & Hab & Hnev & Hbb & Hcom & Hcore & E11 & E19 & E20 & E22 & Hstat & Hz).
pose proof (fe3_geo cx k ly3 S3 W3 _ md3 Hbase HJ Hab)
  as (_ & _ & _ & EFa & _ & _ & H4096 & Hfc & _ & Hs1 & Hs3 & _).
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
destruct (fe3_core_u cx E Hbase Hcore H4096 Hfc Hs3 ltac:(unfold kLowMemEnd in Hs1; lia)) as (U8 & U24 & U25 & _).
pose proof (fe3_base_facts cx Hbase) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpn & Hlen & _).
destruct (fe3_n_facts cx Hlen) as (Hn0 & _).
assert (Hn64 : fe_n cx < 2 ^ 64) by (destruct Hpn as [(Hz0 & _) | (Hz0 & _)]; lia).
pose proof (fe_ss_z_ok cx E PC_s3mid [fe_len_lit (-1)] (w_H W3) ms3 HS U25 Hz) as HSz. clear HS.
eapply (SRr_sym_branch tfibsegs W3 E (fe_ss_z PC_s3mid [fe_len_lit (-1)]) ms3 md3 (POST cx) BC_LTU (SOff 11 0) (SOff 19 0) HSz);
  intros Hbr HS1; cbn [branch_taken] in Hbr; rewrite !fsw_SOff0, E11, E19, bv_ltu_unsigned, !wz in Hbr by lia.
- (* n > 3 MiB: the run reaches the epilogue *)
  fsw_aj_run_toU entry_tbl_ok HS1 HJ HARU PC_epi.
  + exact (fe_awr_z B E [fe_len_lit (-1)] _ _ _ _ _ _ _ _ (fe3_awr cx E [fe_len_lit (-1)] ly3 S3 _ EFa U24 U25 U8)).
  + eapply (fe3_epi_enter POST cx E k ly3 S3 W3 ms3 md3 _ _ _ H9 Hbase HE Hab Hcom Hcore Hstat
      (fe_frame_z E [fe_len_lit (-1)] _ _ HFr) HJ HARU (fe3_same_io_wvb _ _ _) HS1); fe3_conc.
- (* n <= 3 MiB: check_no_overread(data, n) *)
  apply Z.ltb_ge in Hbr.
  fsw_aj_run_toU entry_tbl_ok HS1 HJ HARU A_check_no_overread.
  + exact (fe_awr_z B E [fe_len_lit (-1)] _ _ _ _ _ _ _ _ (fe3_awr cx E [fe_len_lit (-1)] ly3 S3 _ EFa U24 U25 U8)).
  + eapply (fe3_call POST cx E k ly3 S3 W3 ms3 md3 _ _ _ H2 Hbase HE Hab Hnev Hbb Hcom Hcore E19 E20 E22 Hbr Hstat
      (fe_frame_z E [fe_len_lit (-1)] _ _ HFr) HJ HARU (fe3_same_io_wvb _ _ _) HS1); fe3_conc.
Qed.

(* ---- S3 + S4: from memchr's return (C1) to the epilogue (C9) or to check_no_overread's return (C2) ---- *)
Lemma fe_seg3 : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss PC_epi []) (INV_C9 B) ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_cno [fe_len_lit (-1)]) (INV_C2 B) ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_memchr []) (INV_C1 B).
Proof. intros POST H9 H2. apply fe3_seg3_head. exact (fe3_seg3_tail POST H9 H2). Qed.

End s.
