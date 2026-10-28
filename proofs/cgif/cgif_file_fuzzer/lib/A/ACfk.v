(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YC20 YC7x YC21 YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI17 YE00 YE01 YE02 YE03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACfn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACek ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACel ACer ACfm ACf5 ACf9 ACf7 ACf8 ACf6 ACfh ACf4 ACey.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_UNLINK : Z := 0x9c9cc.
Definition RA_UNLINK : Z := 0x80a80.
Definition rt_U_deads : list nat := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 20; 19; 21; 24; 26; 25; 28; 29; 30; 31]%nat.
Definition rt_U_deads_bv : list (bv 5) := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 20; 19; 21; 24; 26; 25; 28; 29; 30; 31]%bv.
Definition RT_UN : nat := 560.
Definition ss_U_0 : sstate :=
mkSS A_UNLINK
(SLit 0 :: SLit RA_UNLINK :: skipn 2 (firstn 10 (ss_regs ss_X_0)) ++ SLit A_PATH :: skipn 11 (ss_regs ss_X_0))
(ss_mem ss_X_0) None (ss_facts ss_X_0).
Definition ss_U : sstate := Eval vm_compute in ss_havoc_regs ss_U_0 RT_UN rt_U_deads.
Definition loop_file (G : YO07.gcfg) (k : nat) (gs : YO07.gif_st) (s : list Z) : list Z :=
concat (YO07.close_gif G (YO07.frames_loop k G gs s)) ++ [59].
Lemma ff_file_loop : forall G loops rest, ff_file G loops rest = loop_file G 16 (gs0 G loops) rest.
Proof. intros. reflexivity. Qed.
Lemma loop_file_step : forall G k gs s attr gen delay tidx nlp lpal img s7,
parse_frame G s = (true, (attr, gen, delay, tidx, nlp, lpal, img), s7) ->
loop_file G (Datatypes.S k) gs s = loop_file G k (YO07.add_frame G gs attr gen delay tidx nlp lpal img) s7.
Proof. intros G k gs s attr gen delay tidx nlp lpal img s7 HP. unfold loop_file. rewrite frames_loop_step, HP. reflexivity. Qed.
Lemma loop_file_stop : forall G k gs s, fst (fst (parse_frame G s)) = false -> loop_file G k gs s = loop_file G 0 gs s.
Proof.
intros G [|k] gs s HP; [reflexivity|]. unfold loop_file. rewrite frames_loop_step.
destruct (parse_frame G s) as [[ok fl] s7]. destruct fl as [[[[[[a ge] d] tq] nq] lp] im]. cbn [fst] in HP. subst ok. reflexivity.
Qed.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Record rtxc := mkRTXC {
x_pl : list byte;
x_aM : Z;
x_K : lleaf -> TSet;
x_G : YO07.gcfg;
x_rest : list Z;
x_gp : Z;
x_f : Z;
x_N : Z }.
Definition FILE_X (xc : rtxc) : list Z := ff_file (x_G xc) 0 (x_rest xc).
Definition fsFIN (cx : rtcx) (xc : rtxc) : Fs.Fs := Fs.fs_set (m_fs (c_md cx)) sink_path (bytes (FILE_X xc)).
Section h.
Variable B : asyms.
Variable wfn : Z.
#[local] Notation rd W ms := (mrestrict (w_H W) (ms_mem ms)).
Lemma xcgif_at_kept : forall (path hw pf : Z) H H' m m' g s1,
xcgif_at tfibsegs wfn path hw pf (mrestrict H m) g s1 -> blk_kept H H' m m' g 96 -> blk_kept H H' m m' (cg_raw s1) 48 ->
(forall fr, In (Some fr) (cg_frames s1) -> blk_kept H H' m m' (fr_ptr fr) 40) ->
xcgif_at tfibsegs wfn path hw pf (mrestrict H' m') g s1.
Proof.
intros path hw pf H H' m m' g s1 (Hg & Hr & Hf) Kg Kr Kf. split; [|split].
- exact (obj_at_blk_kept H H' m m' g LAY_CGIF _ 96 Hg lay_inside_CGIF Kg).
- exact (obj_at_blk_kept H H' m m' (cg_raw s1) LAY_Raw _ 48 Hr lay_inside_Raw Kr).
- intros fr Hin. exact (obj_at_blk_kept H H' m m' (fr_ptr fr) LAY_Frame _ 40 (Hf fr Hin) lay_inside_Frame (Kf fr Hin)).
Qed.
Lemma xcgif_at_blocks_kept : forall (path hw pf : Z) (H H' : word -> bool) (m m' : word -> option byte) g s N,
xcgif_at tfibsegs wfn path hw pf (mrestrict H m) g s ->
(forall b sz, In (b, sz) (cgif_blocks g s N) -> blk_kept H H' m m' b (req_size sz)) ->
xcgif_at tfibsegs wfn path hw pf (mrestrict H' m') g s.
Proof.
intros path hw pf H H' m m' g s N Hat K.
apply (xcgif_at_kept path hw pf H H' m m' g s Hat).
- exact (K g CGIF_SIZE (cgif_blocks_in_g g s N)).
- exact (K (cg_raw s) RAW_SIZE (cgif_blocks_in_raw g s N)).
- intros fr Hf. exact (K (fr_ptr fr) FRAME_SIZE (cgif_blocks_in_frame g s N fr Hf)).
Qed.
Lemma xcgif_at_ngp : forall (path hw pf : Z) m g s, xcgif_at tfibsegs wfn path hw pf m g s -> 0 <= cg_ngp s < 65536.
Proof.
intros path hw pf m g s (Hg & _ & _). cbn [obj_at xcgif_vals LAY_CGIF] in Hg. unfold field_ok in Hg. cbn [fst snd Z.of_N] in Hg.
change (2 ^ (8 * 2)) with 65536 in Hg. tauto.
Qed.
Lemma xcgif_blocks_bsum : forall (path hw pf : Z) m g s N, xcgif_at tfibsegs wfn path hw pf m g s -> cgif_wf s N -> bsum (cgif_blocks g s N) <= CGB.
Proof.
intros path hw pf m g s N Hat Hwf.
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & _ & _).
pose proof (xcgif_at_ngp path hw pf m g s Hat) as Hn. destruct Hat as (Hg & Hr & Hf).
unfold cgif_blocks. rewrite !bsum_cons, bsum_app. cbn [snd].
assert (Hpal : bsum (pal_blocks s) <= 3 * 65536).
{ unfold pal_blocks. destruct (Z.eqb_spec (Z.land (cg_attr s) 4) 0); cbn [bsum fold_right snd]; lia. }
assert (HN0 : 0 <= N) by nia.
assert (Hfr : forall fs, (forall fr, In (Some fr) fs -> obj_at tfibsegs m (fr_ptr fr) LAY_Frame (frame_vals fr)) ->
bsum (frames_blocks N fs) <= Z.of_nat (length fs) * (40 + N + 3 * 65536)).
{ intros fs. induction fs as [|o fs IH]; intros Hfs; [cbn; lia|].
change (frames_blocks N (o :: fs)) with (match o with Some fr => frame_blocks N fr | None => [] end ++ frames_blocks N fs).
rewrite bsum_app. cbn [length]. rewrite Nat2Z.inj_succ.
specialize (IH ltac:(intros fr Hf'; apply Hfs; right; exact Hf')).
destruct o as [fr|].
- pose proof (frame_blocks_bsum m N fr (Hfs fr ltac:(left; reflexivity)) HN0). lia.
- cbn [bsum fold_right]. lia. }
specialize (Hfr (cg_frames s) Hf). rewrite Hlen in Hfr. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hfr.
unfold CGB, CGIF_SIZE, RAW_SIZE. lia.
Qed.
Lemma asink_at_io : forall (K : asink_syms) (m : word -> option byte) (md md' : Model) f Sg,
m_fds md' = m_fds md -> m_fs md' = m_fs md -> asink_at tfibsegs K m md f Sg -> asink_at tfibsegs K m md' f Sg.
Proof.
intros K m md md' f Sg Efd Efs (fd & Wb & Pb & HS & Hok & Hmax & Henv & Hfile & Hhead & Hf0 & Hfs & Hfdl & Huniq).
exists fd, Wb, Pb. rewrite Efd, Efs. repeat (split; [assumption|]). assumption.
Qed.
Lemma cgif_relA_keptX : forall (K : asink_syms) (m m' : word -> option byte) (md md' : Model) g s f N GPAL gs,
(forall b n i, In (b, n) (cgif_blocks g s N ++ [(f, FILE_BLOCK)]) -> 0 <= i < n -> mbyte tfibsegs m' (b + i) = mbyte tfibsegs m (b + i)) ->
(forall a, aenv_addr K a -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
m_fds md' = m_fds md -> m_fs md' = m_fs md ->
cgif_relA tfibsegs K m md s f N GPAL gs -> cgif_relA tfibsegs K m' md' s f N GPAL gs.
Proof.
intros K m m' md md' g s f N GPAL gs Hbl Henv Efd Efs (Hocc & Hsk & Hlive).
assert (KB : forall b n l, In (b, n) (cgif_blocks g s N ++ [(f, FILE_BLOCK)]) -> garr8 tfibsegs m b l -> Z.of_nat (length l) <= n -> garr8 tfibsegs m' b l).
{ intros b n l Hin Hg Hlen. eapply garr8_frame; [exact Hg|]. intros a Ha. replace a with (b + (a - b)) by lia. apply (Hbl b n (a - b) Hin). lia. }
split; [exact Hocc|]. split.
- apply (asink_at_io K m' md md' f _ Efd Efs). eapply asink_at_frame; [|exact Hsk].
intros a [Ha | Ha]; [|exact (Henv a Ha)]. replace a with (f + (a - f)) by lia.
apply (Hbl f FILE_BLOCK (a - f)); [apply in_app_iff; right; left; reflexivity | lia].
- intros HL. destruct (Hlive HL) as (R1 & R2 & R3 & Rpal & Q0 & Q1 & Q2).
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split.
+ intros H4. destruct (Rpal H4) as [Hg Hlen]. split; [|exact Hlen]. apply (KB (cg_pal s) (3 * cg_ngp s) GPAL); [|exact Hg|lia].
apply in_app_iff. left. unfold cgif_blocks. right. right. apply in_app_iff. left. unfold pal_blocks. rewrite (proj2 (Z.eqb_eq _ _) H4). left. reflexivity.
+ assert (FR : forall wg i q, oframe_relbA tfibsegs wg m N (nth i (cg_frames s) None) q -> oframe_relbA tfibsegs wg m' N (nth i (cg_frames s) None) q).
{ intros wg i q Ho. destruct (nth i (cg_frames s) None) as [fr|] eqn:Ei; destruct q as [qf|]; cbn in Ho |- *; try exact Ho.
assert (Hfb : forall b, In b (frame_blocks N fr) -> In b (cgif_blocks g s N ++ [(f, FILE_BLOCK)])).
{ intros b Hb. apply in_app_iff. left. unfold cgif_blocks. right. right. apply in_app_iff. right.
unfold frames_blocks. apply in_flat_map. exists (Some fr). split; [|exact Hb].
rewrite <- Ei. apply nth_In. destruct (Nat.lt_ge_cases i (length (cg_frames s))) as [Hlt|Hge]; [exact Hlt|].
exfalso. rewrite (nth_overflow _ _ Hge) in Ei. discriminate. }
destruct Ho as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & Aimg & Alen & Alp).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
split; [apply (KB (fr_img fr) N); [apply Hfb; unfold frame_blocks; right; left; reflexivity | exact Aimg | lia]|].
split; [exact Alen|].
intros Hb1. destruct (Alp Hb1) as [Hg Hlen]. split; [|exact Hlen].
apply (KB (fr_lpal fr) (3 * fr_nlp fr)); [|exact Hg|lia]. apply Hfb. unfold frame_blocks. right. right.
destruct (Z.eqb_spec (Z.land (fr_attr fr) 1) 0) as [Hz|Hz]; [exfalso; exact (Hb1 Hz) | left; reflexivity]. }
exact (conj (FR _ _ _ Q0) (conj (FR _ _ _ Q1) (FR _ _ _ Q2))).
Qed.
Lemma garr8_of_F2 : forall STK sp0 FP ly S (W : world tfibsegs) mem md own ly3 S3 W3 mem3 md3 k p n l,
ajournal tfibsegs B STK sp0 FP ly S W mem md own ly3 S3 W3 mem3 md3 k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly3 S3) -> (forall i, 0 <= i < req_size n -> ~ inFP FP (p + i)) ->
Z.of_nat (length l) <= n -> n <= req_size n ->
garr8 tfibsegs (mrestrict (w_H W) mem) p l -> garr8 tfibsegs (mrestrict (w_H W3) mem3) p l.
Proof.
intros STK sp0 FP ly S W mem md own ly3 S3 W3 mem3 md3 k p n l HJ Hin Hin3 HnF Hlen Hrq Hg.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
eapply garr8_frame; [exact Hg|]. intros a Ha. apply (mbyte_of_aview tfibsegs). replace a with (p + (a - p)) by lia.
apply (F2 p n (a - p) Hin Hin3); [lia|]. apply HnF. lia.
Qed.
Lemma aj_call_tok : AR_laws tfibsegs B ->
forall W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) spw raw ch1
(KQ : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview tfibsegs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre tfibsegs B STK1 lyc Sc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
SRr tfibsegs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom tfibsegs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK1 (spZ (ms_regs ms)) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved (ms_regs ms) regs2 /\ KQ ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr tfibsegs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal tfibsegs B STK1 (sp0 + o) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved (ms_regs ms) regs2 /\ KQ ly2 S2 W2 regs2 mem2 md2).
Proof.
intros LAWS W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o spw raw ch1 KQ
HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Hrv).
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k (ms_regs ms) STK1 o ch1);
try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub_tok tfibsegs B LAWS tfib_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
End h.
Section j.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XN : xnums.
Variable XL : Z -> Z.
Variable wfn : Z.
#[local] Notation rd W ms := (mrestrict (w_H W) (ms_mem ms)).
Definition rt_xbase2 (cx : rtcx) (xc : rtxc) : Prop :=
rt_xbase B MT XL cx (x_pl xc) (x_aM xc) (x_K xc) /\
ff_cfg (zbytes (x_pl xc)) = Some (x_G xc, 0, x_rest xc) /\ g_opens (x_G xc) = true /\ g_sgct_ok (x_G xc) = true /\
x_N xc = YO07.g_w (x_G xc) * YO07.g_h (x_G xc) /\ 1 <= x_N xc <= 100000000 /\ x_f xc <> 0.
Definition rt_fromX (POST : rtcx -> rtxc -> world tfibsegs -> config -> Prop) (ss : sstate)
(INV : rtcx -> rtxc -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop) : Prop :=
forall (cx : rtcx) (xc : rtxc) (E : env) (k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
rt_base B MT cx -> rt_xbase2 cx xc -> rt_E cx E ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) RTFP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(2, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = [(2, c_fpos cx)] ->
mo_le MT (c_S cx) S3 acc ->
INV cx xc E k acc ly3 S3 W3 ms3 md3 ->
st_ok tfibsegs E ss (restrict (w_H W3) ms3) ->
SRr tfibsegs W3 (mkCfg ms3 md3) (POST cx xc).
Lemma rt_fromX_mono : forall (P Q : rtcx -> rtxc -> world tfibsegs -> config -> Prop) ss INV,
(forall cx xc W c, rt_base B MT cx -> rt_xbase2 cx xc -> P cx xc W c -> Q cx xc W c) ->
rt_fromX P ss INV -> rt_fromX Q ss INV.
Proof.
intros P Q ss INV HPQ HR cx xc E k acc ly3 S3 W3 ms3 md3 HB HX HE HJ Hfr HM HI HS.
eapply SRr_mono; [exact (HR cx xc E k acc ly3 S3 W3 ms3 md3 HB HX HE HJ Hfr HM HI HS)|].
intros W' c' _ HP. exact (HPQ cx xc W' c' HB HX HP).
Qed.
Definition PT (fsU : Fs.Fs) (cx : rtcx) (xc : rtxc) : world tfibsegs -> config -> Prop :=
fun W' c' => AI tfibsegs (w_H W') (w_A W') (cfg_model c') -> srealizes tfibsegs c' (ff_unl (x_K xc) fsU).
Definition PTF (cx : rtcx) (xc : rtxc) : world tfibsegs -> config -> Prop := PT (fsFIN cx xc) cx xc.
Definition ACC_F (xc : rtxc) : Z := RT_NEED1 MT + xn_newgif XN (YO07.g_ngp (x_G xc)) + mo_free MT.
Definition ITER (xc : rtxc) : Z := RFC_COST MT (x_N xc) + xn_addframe XN (x_N xc) + (mo_free MT + mo_free MT).
Definition ACC_G (xc : rtxc) (c : Z) : Z := ACC_F xc + (16 - c) * ITER xc + RFC_COST MT (x_N xc).
Definition ACC_G2 (xc : rtxc) (c : Z) : Z := ACC_G xc c + xn_addframe XN (x_N xc).
Definition ACC_G3 (xc : rtxc) (c : Z) : Z := ACC_F xc + (17 - c) * ITER xc.
Definition ACC_H (xc : rtxc) : Z := ACC_F xc + 16 * ITER xc + RFC_COST MT (x_N xc).
Definition ACC_U (xc : rtxc) : Z := ACC_H xc + xn_close XN (x_N xc).
Definition XROOM (xc : rtxc) (T : Z) : Prop :=
ACC_G xc 1 + xm_addframe XN (x_N xc) <= T /\ ACC_H xc + xm_close XN (x_N xc) <= T.
Definition rt_objX (cx : rtcx) (xc : rtxc) (E : env) (ly3 : alayout) (S3 : astate) (W3 : world tfibsegs) (ms3 : machine_state)
(s : cgif_st) (extra : list (Z * Z)) : Prop :=
ew E 195 = Z_to_bv 64 (x_gp xc) /\ ew E 194 = Z_to_bv 64 (x_N xc) /\ 14 <= c_n cx /\
xcgif_at tfibsegs wfn (ak_path tfib_K) 0 (x_f xc) (rd W3 ms3) (x_gp xc) s /\ cgif_wf s (x_N xc) /\
gcfg_of s (YO07.g_gpal (x_G xc)) = x_G xc /\
Permutation (ablocks B ly3 S3) (cgif_blocks (x_gp xc) s (x_N xc) ++ extra ++ (x_f xc, FILE_BLOCK) :: ablocks B (c_ly cx) (c_S cx)).
Definition rt_relX (xc : rtxc) (W3 : world tfibsegs) (ms3 : machine_state) (md3 : Model) (s : cgif_st) (gs : YO07.gif_st) (q : Z) : Prop :=
cgif_relA tfibsegs tfib_K (rd W3 ms3) md3 s (x_f xc) (x_N xc) (YO07.g_gpal (x_G xc)) gs /\
Z.of_nat (length (concat (YO07.s_out gs))) <= HDR_OUT + q * FRAME_OUT (x_N xc).
Definition LF (xc : rtxc) (k : nat) (gs : YO07.gif_st) (cur : Z) : Prop :=
loop_file (x_G xc) k gs (skipn (Z.to_nat cur) (zbytes (x_pl xc))) = FILE_X xc.
Definition INV_FX : rtcx -> rtxc -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx xc E k acc ly3 S3 W3 ms3 md3 => k <= 14 /\ acc <= ACC_F xc /\
exists s cur gs, rt_objX cx xc E ly3 S3 W3 ms3 s [] /\ rt_stm cx W3 ms3 cur /\
rt_relX xc W3 ms3 md3 s gs 0 /\ LF xc 16 gs cur.
Definition INV_G1X (c : Z) : rtcx -> rtxc -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx xc E k acc ly3 S3 W3 ms3 md3 => k <= 20 + (16 - c) * 55 /\ acc <= ACC_G xc c /\ 1 <= c <= 16 /\ ew E 400 = Z_to_bv 64 c /\
exists s cur lpal lpa img fattr fgen delay nlp tidx gs (IMGV LPALV : list Z),
rt_objX cx xc E ly3 S3 W3 ms3 s (rt_fblocks img (x_N xc) fattr lpa nlp) /\
rt_stm cx W3 ms3 cur /\ rt_fcfg E lpal lpa img fattr fgen delay nlp tidx /\
rt_relX xc W3 ms3 md3 s gs (16 - c) /\
garr8 tfibsegs (rd W3 ms3) img IMGV /\ Z.of_nat (length IMGV) = x_N xc /\
(Z.land fattr 1 <> 0 -> garr8 tfibsegs (rd W3 ms3) lpa LPALV /\ Z.of_nat (length LPALV) = 3 * nlp) /\
LF xc (Z.to_nat c - 1) (YO07.add_frame (x_G xc) gs fattr fgen delay tidx nlp LPALV IMGV) cur.
Definition INV_G2X (c : Z) : rtcx -> rtxc -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx xc E k acc ly3 S3 W3 ms3 md3 => k <= 67 + (16 - c) * 55 /\ acc <= ACC_G2 xc c /\ 1 <= c <= 16 /\ ew E 400 = Z_to_bv 64 c /\
exists s cur lpal lpa img fattr fgen delay nlp tidx gs,
rt_objX cx xc E ly3 S3 W3 ms3 s (rt_fblocks img (x_N xc) fattr lpa nlp) /\
rt_stm cx W3 ms3 cur /\ rt_fcfg E lpal lpa img fattr fgen delay nlp tidx /\
rt_relX xc W3 ms3 md3 s gs (17 - c) /\ LF xc (Z.to_nat c - 1) gs cur.
Definition INV_G3X (c : Z) : rtcx -> rtxc -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx xc E k acc ly3 S3 W3 ms3 md3 => k <= 69 + (16 - c) * 55 /\ acc <= ACC_G3 xc c /\ 1 <= c <= 16 /\ ew E 400 = Z_to_bv 64 c /\
exists s cur gs, rt_objX cx xc E ly3 S3 W3 ms3 s [] /\ rt_stm cx W3 ms3 cur /\
rt_relX xc W3 ms3 md3 s gs (17 - c) /\ LF xc (Z.to_nat c - 1) gs cur.
Definition INV_HX : rtcx -> rtxc -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx xc E k acc ly3 S3 W3 ms3 md3 => k <= 900 /\ acc <= ACC_H xc /\
exists s gs, rt_objX cx xc E ly3 S3 W3 ms3 s [] /\ rt_relX xc W3 ms3 md3 s gs 16 /\
concat (YO07.close_gif (x_G xc) gs) ++ [59] = FILE_X xc.
Definition INV_U (fsU : Fs.Fs) : rtcx -> rtxc -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx xc E k acc ly3 S3 W3 ms3 md3 => k <= EV_LIB /\ acc <= c_T cx /\
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
asink_none tfibsegs tfib_K (rd W3 ms3) md3 /\ m_fs md3 = fsU /\ Fs.fs_sorted fsU = true.
Lemma LF_start : forall xc cur, skipn (Z.to_nat cur) (zbytes (x_pl xc)) = x_rest xc -> LF xc 16 (gs0 (x_G xc) 0) cur.
Proof. intros xc cur H. unfold LF, FILE_X, ff_file, loop_file. rewrite H. reflexivity. Qed.
Lemma LF_step : forall xc k gs cur cur' fattr fgen delay tidx nlp LPALV IMGV,
parse_frame (x_G xc) (skipn (Z.to_nat cur) (zbytes (x_pl xc))) = (true, (fattr, fgen, delay, tidx, nlp, LPALV, IMGV), skipn (Z.to_nat cur') (zbytes (x_pl xc))) ->
LF xc (S k) gs cur -> LF xc k (YO07.add_frame (x_G xc) gs fattr fgen delay tidx nlp LPALV IMGV) cur'.
Proof. intros xc k gs cur cur' fattr fgen delay tidx nlp LPALV IMGV HP HL. unfold LF in *. rewrite <- HL. symmetry. apply loop_file_step. exact HP. Qed.
Lemma LF_stop : forall xc k gs cur, fst (fst (parse_frame (x_G xc) (skipn (Z.to_nat cur) (zbytes (x_pl xc))))) = false ->
LF xc k gs cur -> concat (YO07.close_gif (x_G xc) gs) ++ [59] = FILE_X xc.
Proof. intros xc k gs cur HP HL. unfold LF in HL. rewrite (loop_file_stop _ _ _ _ HP) in HL. exact HL. Qed.
Lemma LF_last : forall xc gs cur, LF xc 0 gs cur -> concat (YO07.close_gif (x_G xc) gs) ++ [59] = FILE_X xc.
Proof. intros xc gs cur HL. exact HL. Qed.
End j.
End e.
Ltac rt_preludeX :=
let LAWS := rnLAWS in let TL := rnTL in let B := lazymatch goal with L : AR_laws tfibsegs ?Bv |- _ => Bv end in
let cx := fresh "cx" in
intros cx xc E k acc ly3 S3 W3 ms3 md3 HBASE HXB HEE HJ3 Hfrs3 HMLE HINV HS;
destruct cx as [ly S W regs mem md p n fpos sp1 E0 T];
pose proof HBASE as HBASE0; pose proof HXB as HXB0;
unfold rt_base in HBASE; unfold rt_E in HEE; red in HINV; unfold rt_F, rt_FL in HBASE, HEE, HJ3, HINV;
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0 c_T] in HBASE, HEE, HJ3, Hfrs3, HMLE, HINV;
destruct HBASE as (HPRE & Hra & Hp & Hn & Hpn & Hfr0 & Hev & Hlive & HROD & Esp1 & EE & EX32 & Usp & HMOK & HNEED);
destruct HEE as (AG & E70 & RF & E87 & E88);
pose proof Hwx_tfa as Hwx; pose proof tfib_segs_low as Hsegs;
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : LLVMF_STK = 32768) by reflexivity;
assert (HEV : EV_LIB = 2000) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
assert (Hn26 : 0 <= n < 2 ^ 26) by (clear - Hpn; destruct Hpn as [[-> _] | [Hn' _]]; lia);
assert (E10 : ew E0 10 = Z_to_bv 64 p) by (rewrite (EE 10%nat 10%bv eq_refl); exact Hp);
assert (E11 : ew E0 11 = Z_to_bv 64 n) by (rewrite (EE 11%nat 11%bv eq_refl); exact Hn);
assert (E2 : ew E0 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl));
pose proof EX32 as E32;
pose proof (proj1 HJ3) as HAR3;
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _);
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p0; unfold flag_addr; pose proof (EFA3 c p0) as X; unfold frame_addr in X; lia);
assert (Hfin3 : In (2, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity);
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres3 & HFSpres3);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as Hfin3_img;
destruct (frames_bounds tfibsegs _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFhigh_img;
change (fs_frame_bytes 2) with 256 in *; change (256 / 8) with 32 in HFSpres3; rewrite !EFA3 in *;
set (F := frame_addr ly 2 fpos) in *; set (FL := flag_addr ly 2 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia);
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia);
let Hsp1r := fresh "Hsp1r" in
destruct (sp1_facts (spZ regs + -128) ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16);
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16;
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by (clear - Hsp1r; lia); clear Hsp1r;
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) (ms_mem ms3) a = aview tfibsegs (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let F1 := fresh "F1" in intros a Ha;
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia);
let Kgot3 := fresh "Kgot3" in let Kcell3 := fresh "Kcell3" in let Kguar3 := fresh "Kguar3" in let Kuar3 := fresh "Kuar3" in
aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3;
destruct xc as [pl aM Kl G rest0 g f N];
unfold rt_xbase2, rt_xbase in HXB; cbn [x_pl x_aM x_K x_G x_rest x_gp x_f x_N] in HXB, HINV |- *;
destruct HXB as ((Hnpl & HPL0 & HSNK0 & HFD0 & HSORT0 & HAM0 & HLEAF & HTX) & HCFG & HOPENS & HSGCT & HNG & HN1 & Hf0);
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_T] in Hnpl, HPL0, HSNK0, HFD0, HSORT0, HAM0, HTX, HLEAF.
Ltac xcb := cbn [x_pl x_aM x_K x_G x_rest x_gp x_f x_N] in *.
Ltac xacc := unfold XROOM, ACC_U, ACC_H, ACC_G3, ACC_G2, ACC_G, ACC_F, ITER, RFC_COST in *; cbn [x_pl x_aM x_K x_G x_rest x_gp x_f x_N c_T] in *.
Ltac rt_handX RC HS :=
lazymatch goal with |- SRr _ ?W3 (mkCfg ?ms3 ?md3) (?PP ?cxv ?xcv) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply (RC cxv xcv Ev _ _ _ _ W3 ms3 md3);
[ lazymatch goal with H0 : rt_base _ _ _ |- _ => exact H0 end
| lazymatch goal with H0 : rt_xbase2 _ _ _ _ _ |- _ => exact H0 end
| repeat (lazymatch goal with |- rt_E _ (havoc _ _ _) => apply rt_E_havoc; [clear; cbn; lia|] | |- rt_E _ (ewset _ _ _) => apply rt_E_ewset; [clear; cbn; lia|] end);
unfold rt_E, rt_F, rt_FL; cbn [c_ly c_fpos c_E0 c_sp1];
split; [assumption|]; repeat (split; [eassumption|]); eassumption
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| red; cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0 c_T x_pl x_aM x_K x_G x_rest x_gp x_f x_N]
| exact HS ] end end.
