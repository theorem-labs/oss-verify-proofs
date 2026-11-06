(* write_value's CONTAINER arms (fs.asan image A, write_value 0x83d84): the writer facts across ONE CALL of a writer
   callee (put, indent, put_string or write_value): from the invariant's writer facts at the call (ZZwv_inv.wvc_sem)
   and the callee's post (the four specs share it: wout_ok, wbudget_kept, bswap, wkeep, fs_glob, and the callee's
   journal with uswap), the writer facts at the return, against the model state with the callee's pieces appended.
   Template (not a copied proof): the bespoke ASan proof a working branch lib/A/Prog/write_value_cont.v
   (wvc_keep 296-310, wvc_lam_keep 696-720, wvc_node_keep 541-548: the facts one writer step keeps).
   Rule 24: no function proved here (write_value's lookup: lane record (internal path), CHECKER CONFIRM
   a Theorem Labs lane). *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat
FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model FSW_writer_kit
FSH_Fn_reader FSW_rd FSupoisonStack FSW_pj ZZwv_defs ZZwv_inv ZZwv_kit ZZwv_call.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- list facts ---- *)
Lemma wvc_pairwise_mid : forall {X : Type} (R : X -> X -> Prop) (l1 l2 : list X) (y x : X),
  pairwise R (l1 ++ y :: l2) -> In x (l1 ++ l2) -> R x y \/ R y x.
Proof.
intros X R l1. induction l1 as [|z l1 IH]; intros l2 y x HP Hin.
- cbn in HP, Hin. destruct HP as [HF _]. right. rewrite Forall_forall in HF. exact (HF x Hin).
- cbn in HP, Hin. destruct HP as [HF HP]. destruct Hin as [<- | Hin].
  + left. rewrite Forall_forall in HF. apply HF. apply in_or_app. right. left. reflexivity.
  + exact (IH l2 y x HP Hin).
Qed.

Lemma wvc_zdisj_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. lia. Qed.

(* an image range checked by computation (FSW_write_value.wv_img_cover's statement and proof) *)
Lemma wvc_img_cover : forall c n,
  existsb (fun s => (Z.of_N (seg_base s) <=? c) && (c + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true ->
  forall a, c <= a < c + n -> in_img tfibsegs a.
Proof.
intros c n H a Ha. apply existsb_exists in H as (s & Hin & Hb). apply andb_true_iff in Hb as [H0 H1].
apply Z.leb_le in H0. apply Z.leb_le in H1.
exists s. split; [exact Hin|]. lia.
Qed.

(* the FS_PSTAT_FP statics are not read-only bytes *)
Lemma wvc_pstat_not_ro : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Hro (r & Hr & Hlo & Hhi). cbv [FS_PSTAT_FP In] in Hr.
destruct Hro as [(sg & Hin & Hw & Hs) | Hs].
- change tfibsegs with [Asan.Asan_segment_000; Asan.Asan_segment_001; Asan.Asan_segment_002; Asan.Asan_segment_003]
    in Hin.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
    cbn [fst snd] in *; vm_compute in Hw; try discriminate; cbn in Hs; lia.
- destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in *; unfold FS_RLO, FS_RHI in *; lia.
Qed.

(* the writer footprint at a call: the statics, or the live buffer's whole block *)
Lemma wvc_fp_cases : forall buf cap a, inFP (FS_PSTAT_FP ++ wbuf_fp buf cap) a ->
  inFP FS_PSTAT_FP a \/ (cap <> 0 /\ buf - HEAD <= a < buf + cap).
Proof.
intros buf cap a H. apply inFP_app in H as [H|H]; [left; exact H|right].
unfold wbuf_fp in H. destruct (Z.eqb_spec cap 0) as [E|E]; [exact (False_ind _ (inFP_nil a H))|].
destruct H as (r & [<-|[]] & H1 & H2). cbn [fst snd] in *. split; [exact E | lia].
Qed.

Lemma wvc_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Hlo & Hhi). cbv [FS_PSTAT_FP In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in *.
- apply (wvc_img_cover 0xa3ca0 8 ltac:(vm_compute; reflexivity)). lia.
- apply (wvc_img_cover 0x5da5c0 8 ltac:(vm_compute; reflexivity)). lia.
- apply (wvc_img_cover 0x5da5e0 8 ltac:(vm_compute; reflexivity)). lia.
- apply (wvc_img_cover 0x5da600 8 ltac:(vm_compute; reflexivity)). lia.
Qed.


Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* two entries at different places of a live-block list are disjoint *)
Lemma wvc_mid_apart : forall ly S (W : world tfibsegs) mx md C1 C2 y x,
  AR tfibsegs B ly S W mx md -> ablocks B ly S = C1 ++ y :: C2 -> In x (C1 ++ C2) ->
  zdisjoint (fst y, req_size (snd y)) (fst x, req_size (snd x)).
Proof.
intros ly S W mx md C1 C2 [yp yn] [xp xn] HAR E Hin.
assert (Hy : In (yp, yn) (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md yp yn HAR Hy) as (_ & _ & _ & _ & _ & Hpw & _).
rewrite E, map_app in Hpw. cbn [map] in Hpw.
assert (Hx : In (xp, req_size xn) (map (fun b : Z * Z => (fst b, req_size (snd b))) C1 ++
                                    map (fun b : Z * Z => (fst b, req_size (snd b))) C2)).
{ rewrite <- map_app. exact (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ (xp, xn) Hin). }
destruct (wvc_pairwise_mid zdisjoint _ _ _ _ Hpw Hx) as [H | H]; cbn [fst snd] in *;
  [exact (wvc_zdisj_sym _ _ H) | exact H].
Qed.

(* after a writer call, every other block of the old list is still live and apart from the new buffer's block *)
Lemma wvc_bswap_fresh : forall ly' S' (W' : world tfibsegs) mx' md' A buf buf' cap cap' x,
  AR tfibsegs B ly' S' W' mx' md' ->
  bswap A (ablocks B ly' S') buf buf' cap cap' -> In x A -> x <> (buf - HEAD, cap + HEAD) ->
  (cap' <> 0 -> In (buf' - HEAD, cap' + HEAD) (ablocks B ly' S')) ->
  In x (ablocks B ly' S') /\
  (cap' <> 0 -> zdisjoint (buf' - HEAD, req_size (cap' + HEAD)) (fst x, req_size (snd x))).
Proof.
intros ly' S' W' mx' md' A buf buf' cap cap' x HAR HBS Hin Hne Hnew.
destruct HBS as [(Eb & Ec & EA) | [(Ec0 & C1 & C2 & EA' & EC) | (A1 & A2 & C1 & C2 & EA & EA' & EC)]].
- rewrite EA. split; [exact Hin|]. intros Hc.
  subst buf' cap'. pose proof (Hnew Hc) as Hb. rewrite EA in Hb.
  pose proof (sep_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly' S' W' mx' md' (buf - HEAD) (cap + HEAD) (fst x) (snd x)
    HAR (ltac:(rewrite EA; exact Hb)) (ltac:(rewrite EA; destruct x; exact Hin))
    (ltac:(intros E; apply Hne; destruct x; cbn [fst snd] in E; rewrite E; reflexivity))) as Hd.
  exact Hd.
- assert (Hx : In x (C1 ++ C2)) by (rewrite EC; exact Hin).
  split; [rewrite EA'; apply in_or_app; apply in_app_or in Hx; destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; exact Hx]|].
  intros _. exact (wvc_mid_apart ly' S' W' mx' md' C1 C2 (buf' - HEAD, cap' + HEAD) x HAR EA' Hx).
- assert (Hx : In x (C1 ++ C2)).
  { rewrite EC. rewrite EA in Hin. apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [Hx | [Hx | Hx]]; [left; exact Hx | exfalso; apply Hne; symmetry; exact Hx | right; exact Hx]. }
  split; [rewrite EA'; apply in_or_app; apply in_app_or in Hx; destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; exact Hx]|].
  intros _. exact (wvc_mid_apart ly' S' W' mx' md' C1 C2 (buf' - HEAD, cap' + HEAD) x HAR EA' Hx).
Qed.

(* ---- the tree's footprint at a call is off the writer's footprint (the statics and the live buffer's block) ---- *)
Lemma wvc_foot_off_fp : forall ly S (W : world tfibsegs) mx md m v D buf cap,
  AR tfibsegs B ly S W mx md -> FSH_Fn_reader.pobj tfibsegs B ly S W m v ->
  ublocks_ok B tfibsegs ly S W m D -> (forall a k, In (a, k) D -> a <> buf) ->
  (cap <> 0 -> v + 56 <= buf - HEAD \/ buf + cap <= v) ->
  (cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S)) -> 0 <= cap ->
  forall x, PjStruct.pj_foot v D x -> ~ inFP (FS_PSTAT_FP ++ wbuf_fp buf cap) x.
Proof.
intros ly S W mx md m v D buf cap HAR HPO HUL HD HR HBIN Hc x Hf Hin.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (wvc_fp_cases buf cap x Hin) as [Hs | (Hc0 & H1 & H2)].
- apply wvc_pstat_img in Hs.
  destruct Hf as [Hv | ((a0 & k0) & Hb & Hh)].
  + exact (zwk_t_pobj_img B ly S W mx md m v HAR HPO x Hv Hs).
  + destruct (HUL a0 k0 Hb) as (Hin0 & _ & Hk0 & _). unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
    pose proof (req_size_pos (k0 + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ).
    exact (blk_img tfibsegs B LAWS ly S W mx md (a0 - HEAD) (k0 + HEAD) x HAR Hin0 ltac:(unfold HEAD in *; lia) Hs).
- destruct Hf as [Hv | ((a0 & k0) & Hb & Hh)].
  + destruct (HR Hc0); lia.
  + destruct (HUL a0 k0 Hb) as (Hin0 & _ & Hk0 & _). unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
    pose proof (HBIN Hc0) as Hbb.
    assert (Hne : (a0 - HEAD, k0 + HEAD) <> (buf - HEAD, cap + HEAD)).
    { intros E. injection E as E1 _. apply (HD a0 k0 Hb). lia. }
    pose proof (sep_blocks tfibsegs B LAWS ly S W mx md _ _ _ _ HAR Hin0 Hbb Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    pose proof (req_size_pos (k0 + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ1).
    pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ2).
    unfold HEAD in *. lia.
Qed.

(* ---- a block covering a byte of the footprint stays live across the call ---- *)
Lemma wvc_foot_live : forall ly S ly' S' (W W' : world tfibsegs) mx md mx' md' v D buf buf' cap cap',
  AR tfibsegs B ly S W mx md -> AR tfibsegs B ly' S' W' mx' md' ->
  bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap cap' ->
  (cap' <> 0 -> In (buf' - HEAD, cap' + HEAD) (ablocks B ly' S')) ->
  (cap = 0 -> buf = 0) -> 0 <= cap ->
  (forall x, PjStruct.pj_foot v D x -> ~ inFP (FS_PSTAT_FP ++ wbuf_fp buf cap) x) ->
  forall b n x, In (b, n) (ablocks B ly S) -> b <= x < b + req_size n -> PjStruct.pj_foot v D x ->
    In (b, n) (ablocks B ly' S').
Proof.
intros ly S ly' S' W W' mx md mx' md' v D buf buf' cap cap' HAR HAR' HBS Hnew Hb0 Hc HFOOT b n x Hin Hx Hf.
assert (Hne : (b, n) <> (buf - HEAD, cap + HEAD)).
2: { exact (proj1 (wvc_bswap_fresh ly' S' W' mx' md' _ buf buf' cap cap' (b, n) HAR' HBS Hin Hne Hnew)). }
intros E. injection E as Eb En.
destruct (Z.eq_dec cap 0) as [E0 | E0].
- rewrite (Hb0 E0) in Eb. destruct (fsw_ablock_low B ly S W mx md b n HAR Hin) as (A1 & _). unfold HEAD in *. lia.
- apply (HFOOT x Hf). apply inFP_app. right. unfold wbuf_fp. destruct (Z.eqb_spec cap 0) as [E1|E1]; [lia|].
  exists (buf - HEAD, buf + cap). split; [left; reflexivity|]. cbn [fst snd]. subst b n.
  unfold req_size, HEAD in *. destruct (Z.eqb_spec (cap + 16) 0); lia.
Qed.

(* ---- the tree's own blocks stay live, and none is the new buffer ---- *)
Lemma wvc_D_live : forall ly S ly' S' (W W' : world tfibsegs) mx' md' m D buf buf' cap cap',
  AR tfibsegs B ly' S' W' mx' md' ->
  bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap cap' ->
  (cap' <> 0 -> In (buf' - HEAD, cap' + HEAD) (ablocks B ly' S')) -> 0 <= cap' ->
  ublocks_ok B tfibsegs ly S W m D -> (forall a k, In (a, k) D -> a <> buf) ->
  forall a kk, In (a, kk) D -> In (a - HEAD, kk + HEAD) (ablocks B ly' S') /\ (cap' <> 0 -> a <> buf').
Proof.
intros ly S ly' S' W W' mx' md' m D buf buf' cap cap' HAR' HBS Hnew Hc' HUL HD a kk Hak.
destruct (HUL a kk Hak) as (Hin0 & _ & Hk & _).
assert (Hne : (a - HEAD, kk + HEAD) <> (buf - HEAD, cap + HEAD)).
{ intros E. injection E as E1 _. apply (HD a kk Hak). lia. }
destruct (wvc_bswap_fresh ly' S' W' mx' md' _ buf buf' cap cap' _ HAR' HBS Hin0 Hne Hnew) as (Hin' & Hd).
split; [exact Hin'|]. intros Hc E. specialize (Hd Hc). unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (req_size_pos (kk + HEAD) ltac:(unfold HEAD; lia)) as (RQ1 & _).
pose proof (req_size_pos (cap' + HEAD) ltac:(unfold HEAD; lia)) as (RQ2 & _).
subst a. unfold HEAD in *. lia.
Qed.

(* ---- the root node is apart from the new buffer ---- *)
Lemma wvc_root_fresh : forall ly S ly' S' (W W' : world tfibsegs) mx md mx' md' m v buf buf' cap cap',
  AR tfibsegs B ly S W mx md -> AR tfibsegs B ly' S' W' mx' md' ->
  (forall cid pos, In (cid, pos) (frames S) -> In (cid, pos) (frames S') /\ frame_addr ly' cid pos = frame_addr ly cid pos) ->
  bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap cap' ->
  (cap' <> 0 -> In (buf' - HEAD, cap' + HEAD) (ablocks B ly' S')) -> 0 <= cap' ->
  FSH_Fn_reader.pobj tfibsegs B ly S W m v ->
  (cap <> 0 -> v + 56 <= buf - HEAD \/ buf + cap <= v) -> (cap = 0 -> buf = 0) -> 0 <= cap ->
  cap' <> 0 -> v + 56 <= buf' - HEAD \/ buf' + cap' <= v.
Proof.
intros ly S ly' S' W W' mx md mx' md' m v buf buf' cap cap' HAR HAR' HFR HBS Hnew Hc' HPO HR Hb0 Hc Hc0'.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (RQ : req_size (cap' + HEAD) = cap' + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (cap' + 16) 0); lia).
destruct HPO as ([((cid & pos & Hin & Hc1 & Hal & Hlo & Hhi) & _ & _) | ((b & mm & Hin & Hlo & Hhi) & _ & _)] & _).
- destruct (HFR cid pos Hin) as (Hin' & Efa).
  pose proof (sep_block_frame tfibsegs B LAWS ly' S' W' mx' md' _ _ cid pos HAR' (Hnew Hc0') Hin') as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite RQ, Efa in Hd. unfold HEAD in *. lia.
- assert (Hne : (b, mm) <> (buf - HEAD, cap + HEAD)).
  { intros E. injection E as Eb Em. destruct (Z.eq_dec cap 0) as [E0|E0].
    - rewrite (Hb0 E0) in Eb. destruct (fsw_ablock_low B ly S W mx md b mm HAR Hin) as (A1 & _). unfold HEAD in *. lia.
    - subst b mm. destruct (HR E0); unfold req_size, HEAD in *; destruct (Z.eqb_spec (cap + 16) 0); lia. }
  destruct (wvc_bswap_fresh ly' S' W' mx' md' _ buf buf' cap cap' _ HAR' HBS Hin Hne Hnew) as (_ & Hd).
  specialize (Hd Hc0'). unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite RQ in Hd. unfold HEAD in *. lia.
Qed.

(* ---- the writer footprint's three side facts at a call: below the low shadow or above the high shadow, the sink
   closed (every range starts above 0), and off the read-only bytes ---- *)
Lemma wvc_fp_aux : forall ly S (W : world tfibsegs) mx md buf cap,
  AR tfibsegs B ly S W mx md -> (cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S)) -> 0 <= cap ->
  (forall x, inFP (FS_PSTAT_FP ++ wbuf_fp buf cap) x -> x < kLowShadowBeg \/ kHighShadowEnd <= x) /\
  ~ YI16.sink_open_fp (FS_PSTAT_FP ++ wbuf_fp buf cap) /\
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP (FS_PSTAT_FP ++ wbuf_fp buf cap) a).
Proof.
intros ly S W mx md buf cap HAR HBIN Hc.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split].
- intros x Hx. destruct (wvc_fp_cases buf cap x Hx) as [Hs | (Hc0 & H1 & H2)].
  + pose proof (fs_segs_img x (wvc_pstat_img x Hs)) as L. left. unfold FS_IMG_END, kLowShadowBeg in *. lia.
  + destruct (al_blocks tfibsegs B LAWS ly S W mx md _ _ HAR (HBIN Hc0)) as (_ & _ & _ & Happ & _).
    pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ).
    unfold in_app in Happ. unfold kHighShadowEnd, kHighMemBeg, kLowShadowBeg, HEAD in *. lia.
- apply sink_closed_pos. apply Forall_app. split.
  + cbv [FS_PSTAT_FP]. repeat constructor; cbn [fst]; lia.
  + unfold wbuf_fp. destruct (Z.eqb_spec cap 0) as [E|E]; [constructor|].
    destruct (fsw_ablock_low B ly S W mx md _ _ HAR (HBIN E)) as (A1 & _).
    constructor; [cbn [fst]; unfold HEAD in *; lia | constructor].
- intros a Hro Hin. destruct (wvc_fp_cases buf cap a Hin) as [Hs | (Hc0 & H1 & H2)].
  + exact (wvc_pstat_not_ro a Hro Hs).
  + pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ).
    exact (blk_img tfibsegs B LAWS ly S W mx md _ _ a HAR (HBIN Hc0) ltac:(unfold HEAD in *; lia) (fsw_roP_img a Hro)).
Qed.

End C.
