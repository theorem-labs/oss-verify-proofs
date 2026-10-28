(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 UI5c UI21 UI3u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition gcfg_of (s : cgif_st) (GPAL : list Z) : YO07.gcfg :=
YO07.mkG (cg_W s) (cg_H s) (cg_attr s) (cg_gen s) (cg_ngp s) GPAL.
Definition frame_relb (wg : bool) (mem : word -> option byte) (N : Z) (f : frame_st) (fr : YO07.frame) : Prop :=
fr_attr f = YO07.f_attr fr /\ (if wg then fr_gen f = YO07.f_gen fr else True) /\ fr_delay f = YO07.f_delay fr /\ fr_nlp f = YO07.f_nlp fr /\
(Z.land (fr_attr f) 6 <> 0 -> fr_ctidx f = YO07.f_ctrans fr) /\ fr_disp f = YO07.f_disp fr /\ fr_tidx f = YO07.f_trans fr /\
garr8 ubs0segs mem (fr_img f) (YO07.f_img fr) /\ Z.of_nat (length (YO07.f_img fr)) = N /\
(Z.land (fr_attr f) 1 <> 0 -> garr8 ubs0segs mem (fr_lpal f) (YO07.f_lpal fr) /\ Z.of_nat (length (YO07.f_lpal fr)) = 3 * fr_nlp f).
Definition oframe_relb (wg : bool) (mem : word -> option byte) (N : Z) (o : option frame_st) (q : option YO07.frame) : Prop :=
match o, q with
| None, None => True
| Some f, Some fr => frame_relb wg mem N f fr
| _, _ => False
end.
Lemma oframe_relb_occ : forall wg mem N o q, oframe_relb wg mem N o q -> (o = None <-> q = None).
Proof using. intros wg mem N [f|] [fr|] H; cbn [oframe_relb] in H; split; intros E; try reflexivity; try discriminate E; destruct H. Qed.
Definition frame_rel := frame_relb true.
Definition frame_rel0 := frame_relb false.
Definition oframe_rel := oframe_relb true.
Definition oframe_rel0 := oframe_relb false.
Lemma frame_relb_weaken : forall wg mem N f fr, frame_relb wg mem N f fr -> frame_relb false mem N f fr.
Proof using. intros wg mem N f fr (A1 & A2 & H). split; [exact A1|]. split; [exact I | exact H]. Qed.
Lemma oframe_relb_weaken : forall wg mem N o q, oframe_relb wg mem N o q -> oframe_relb false mem N o q.
Proof using. intros wg mem N [f|] [fr|] H; cbn in H |- *; try exact H. eapply frame_relb_weaken; exact H. Qed.
Definition cgif_live (gs : YO07.gif_st) : Prop := YO07.s_cur gs = YO07.C_OK \/ YO07.s_cur gs = YO07.C_PENDING.
Definition cgif_occ (s : cgif_st) (gs : YO07.gif_st) : Prop :=
(nth 0 (cg_frames s) None = None <-> YO07.s_q0 gs = None) /\
(nth 1 (cg_frames s) None = None <-> YO07.s_q1 gs = None) /\
(nth 2 (cg_frames s) None = None <-> YO07.s_q2 gs = None).
Definition cgif_rel (mem : word -> option byte) (md : Model) (s : cgif_st) (N : Z) (GPAL : list Z) (gs : YO07.gif_st) : Prop :=
(rc_int (cg_cur s) = YO07.s_cur gs /\ cgif_occ s gs) /\
sink_at ubs0_msyms mem md (cg_file s) (concat (YO07.s_out gs)) /\
(cgif_live gs ->
rc_int (rw_cur s) = YO07.s_rcur gs /\ rw_attr s = raw_attr_of (cg_attr s) /\ cg_ihead s = YO07.s_ihead gs /\
(Z.land (cg_attr s) 4 = 0 -> garr8 ubs0segs mem (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s) /\
oframe_relb false mem N (nth 0 (cg_frames s) None) (YO07.s_q0 gs) /\
oframe_relb true mem N (nth 1 (cg_frames s) None) (YO07.s_q1 gs) /\
oframe_relb true mem N (nth 2 (cg_frames s) None) (YO07.s_q2 gs)).
Definition af_attempts_alloc (g : YO07.gcfg) (gs : YO07.gif_st) (attr delay : Z) (nf : YO07.frame) (img : list Z) : bool :=
if negb (YO07.s_cur gs =? YO07.C_OK) && negb (YO07.s_cur gs =? YO07.C_PENDING) then false
else
let hasAlpha := YO07.flag (YO07.g_attr g) 8 || YO07.flag attr 2 in
let hasSet := YO07.flag attr 4 in
if (hasAlpha && hasSet) || (YO07.flag (YO07.g_attr g) 8 && YO07.flag attr 2) || (negb (YO07.flag attr 1) && YO07.flag (YO07.g_attr g) 4) then false
else
match YO07.q_get gs (YO07.s_ihead gs) with
| Some hd =>
let fd := delay + YO07.f_delay hd in
if (fd <=? 65535) && negb (YO07.flag (YO07.g_gen g) 1) then
let same := if negb (YO07.flag attr 1) && negb (YO07.flag (YO07.f_attr hd) 1) && negb (YO07.flag attr 4) && negb (YO07.flag (YO07.f_attr hd) 4)
then YO07.list_eqb img (YO07.f_img hd)
else forallb (fun pq => negb (YO07.cmp_pixel g nf hd (fst pq) (snd pq))) (combine img (YO07.f_img hd)) in
negb same
else true
| None => true
end.
Definition C_EALLOC : Z := 2.
Definition af_cut (g : YO07.gcfg) (gs gs' : YO07.gif_st) (attr gen delay ctrans nlp : Z) (lpal img : list Z) : Prop :=
af_attempts_alloc g gs attr delay (YO07.new_frame g attr gen delay ctrans nlp lpal img) img = true /\
YO07.s_cur gs' = C_EALLOC /\
(YO07.s_out gs' = YO07.s_out gs \/ YO07.s_out gs' = YO07.s_out (YO07.add_frame g gs attr gen delay ctrans nlp lpal img)).
Definition close_fl (g : YO07.gcfg) (st : YO07.gif_st * bool) (i : Z) : YO07.gif_st * bool :=
let '(s0, stop) := st in
if stop then st
else match YO07.q_get s0 i with
| None => st
| Some f =>
let '(r, bytes) := YO07.flush_frame g (YO07.s_rcur s0) f (YO07.q_get s0 (i - 1)) in
(YO07.mkS (YO07.s_q0 s0) (YO07.s_q1 s0) (YO07.s_q2 s0) (YO07.s_ihead s0) (YO07.s_cur s0) r
(if r =? YO07.C_OK then YO07.s_out s0 ++ [bytes] else YO07.s_out s0), negb (r =? YO07.C_OK))
end.
Lemma close_gif_fl : forall g s,
YO07.close_gif g s = YO07.s_out (if YO07.s_cur s =? YO07.C_OK then fst (close_fl g (close_fl g (s, false) 1) 2) else s).
Proof using. intros g s. reflexivity. Qed.
Definition close_attempts (g : YO07.gcfg) (gs : YO07.gif_st) : list YO07.gif_st :=
if YO07.s_cur gs =? YO07.C_OK then
(match YO07.q_get gs 1 with Some _ => [gs] | None => [] end) ++
(let st1 := close_fl g (gs, false) 1 in
if snd st1 then [] else match YO07.q_get (fst st1) 2 with Some _ => [fst st1] | None => [] end)
else [].
Definition close_out (g : YO07.gcfg) (gs : YO07.gif_st) (OUT : list (list Z)) : Prop :=
OUT = YO07.close_gif g gs \/ exists st, In st (close_attempts g gs) /\ OUT = YO07.s_out st.
Section b.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition newgif_specV : Prop :=
forall L A (regs : bvmap 5 word) mem md (cfgp pal0 pala attr gen W H ngp loops : Z) (rest : list (Z * Z)) (GPAL : list Z),
fn_pre ubs0_msyms MR NEWGIF_STK L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 cfgp -> cfgp mod 8 = 0 -> spZ regs <= cfgp -> cfgp + 48 <= 2 ^ 63 ->
obj_at ubs0segs mem cfgp LAY_Config [pal0; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0] ->
sink_none ubs0_msyms mem md ->
spZ regs <= 2 ^ 47 ->
W * H <= 100000000 ->
Z_to_bv 64 pala = Z_to_bv 64 pal0 ->
Permutation (blocks L A) ((if Z.land attr 4 =? 0 then [(pala, 3 * ngp)] else []) ++ rest) ->
(Z.land attr 4 = 0 -> garr8 ubs0segs mem pala GPAL /\ Z.of_nat (length GPAL) = 3 * ngp) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_cgif_newgif) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md' (res : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR NEWGIF_STK (spZ regs) [sink_token] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
getr regs' 10 = Z_to_bv 64 res /\
((res = 0 /\ (exists leak, Permutation (blocks L' A') (leak ++ blocks L A)) /\
sink_none ubs0_msyms mem' md' /\
(Fs.fs_lookup (m_fs md') sink_path = Fs.fs_lookup (m_fs md) sink_path \/
(W <> 0 /\ H <> 0 /\ Fs.fs_lookup (m_fs md') sink_path = Some (bytes [])))) \/
(res <> 0 /\ exists s,
(exists S', sink_at ubs0_msyms mem' md' (cg_file s) S' /\ Z.of_nat (length S') <= HDR_OUT) /\
cgif_at mem' res s /\ cgif_wf s (W * H) /\
cg_frames s = [None; None; None] /\ cg_W s = W /\ cg_H s = H /\ cg_attr s = attr /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\
Permutation (blocks L' A') (cgif_blocks res s (W * H) ++ blocks L A) /\
cg_gen s = gen /\ cg_ngp s = ngp /\ cgif_rel mem' md' s (W * H) GPAL (gs_new W H attr ngp loops GPAL) /\
Z.of_nat (length (concat (YO07.s_out (gs_new W H attr ngp loops GPAL)))) <= HDR_OUT))).
Definition addframe_specV : Prop :=
forall L A (regs : bvmap 5 word) mem md (g cfp : Z) (s : cgif_st) (N : Z)
(lpal lpa img fattr fgen delay nlp tidx : Z) (rest : list (Z * Z)) (GPAL IMG LPAL : list Z) (gs : YO07.gif_st),
fn_pre ubs0_msyms MR ADDFRAME_STK L A regs mem md -> st_init_done A = true ->
Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N <= SINK_MAX ->
spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 cfp ->
cfp mod 8 = 0 -> spZ regs <= cfp -> cfp + 32 <= 2 ^ 63 ->
obj_at ubs0segs mem cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cgif_at mem g s -> cgif_wf s N ->
Z_to_bv 64 lpa = Z_to_bv 64 lpal ->
Permutation (blocks L A)
(cgif_blocks g s N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) ->
cgif_rel mem md s N GPAL gs ->
garr8 ubs0segs mem img IMG -> Z.of_nat (length IMG) = N ->
(Z.land fattr 1 <> 0 -> garr8 ubs0segs mem lpa LPAL /\ Z.of_nat (length LPAL) = 3 * nlp) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_cgif_addframe) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md' (s' : cgif_st),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR ADDFRAME_STK (spZ regs) (cgif_fp g s N) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
cgif_at mem' g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s /\ cg_H s' = cg_H s /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\ cg_file s' = cg_file s /\
Permutation (blocks L' A')
(cgif_blocks g s' N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) /\
cg_gen s' = cg_gen s /\ cg_ngp s' = cg_ngp s /\ cg_pal s' = cg_pal s /\
(exists gs', cgif_rel mem' md' s' N GPAL gs' /\
Z.of_nat (length (concat (YO07.s_out gs'))) <= Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N /\
(gs' = YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG
\/ af_cut (gcfg_of s GPAL) gs gs' fattr fgen delay tidx nlp LPAL IMG))).
Definition close_specV : Prop :=
forall L A (regs : bvmap 5 word) mem md (g : Z) (s : cgif_st) (N : Z) (rest : list (Z * Z)) (GPAL : list Z) (gs : YO07.gif_st),
fn_pre ubs0_msyms MR CLOSE_STK L A regs mem md -> st_init_done A = true ->
Z.of_nat (length (concat (YO07.s_out gs))) + CLOSE_OUT N <= SINK_MAX ->
spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 g ->
cgif_at mem g s -> cgif_wf s N ->
Permutation (blocks L A) (cgif_blocks g s N ++ rest) ->
cgif_rel mem md s N GPAL gs ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_cgif_close) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR CLOSE_STK (spZ regs) (cgif_fp g s N) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
sink_none ubs0_msyms mem' md' /\
Permutation (blocks L' A') rest /\
(exists OUT, close_out (gcfg_of s GPAL) gs OUT /\ Fs.fs_lookup (m_fs md') sink_path = Some (bytes (concat OUT ++ [59])))).
End b.
End a.
