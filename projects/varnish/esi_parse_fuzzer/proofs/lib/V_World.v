(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7 V_AKit V_Vsb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.

Module V_VepKit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7 V_AKit V_Vsb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Lemma testbit_small : forall a n, 0 <= a < 2^n -> 0 <= n -> forall m, n <= m -> Z.testbit a m = false.
Proof.
  intros a n Ha Hn m Hm. destruct (Z.eq_dec a 0) as [->|NZ]. { apply Z.bits_0. }
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
  apply (Z.lt_le_trans _ (2^n)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma testbit_mask8 : forall k m, 0 <= k -> 0 <= m ->
  Z.testbit (Z.shiftl (Z.ones 8) k) m = ((k <=? m) && (m <? k + 8))%bool.
Proof.
  intros k m Hk Hm.
  destruct (Z.ltb_spec m k).
  - rewrite Z.shiftl_spec_low by lia. destruct (Z.leb_spec k m); [lia|reflexivity].
  - rewrite Z.shiftl_spec by lia. destruct (Z.leb_spec k m); [|lia]. cbn [andb].
    destruct (Z.ltb_spec m (k + 8)).
    + apply Z.ones_spec_low. lia.
    + apply Z.ones_spec_high. lia.
Qed.

(* [comment removed for export] *)
Lemma be64_redecode : forall l, 0 <= l < 2^62 ->
  Z.lor (Z.shiftl (Z.lor (Z.lor (Z.lor (Z.land (l / 4294967296) 16711680)
                                        (Z.shiftl (l / 72057594037927936) 24 mod 18446744073709551616))
                                (Z.land (l / 4294967296) 65280))
                         (Z.land (l / 4294967296) 255)) 32 mod 18446744073709551616)
        (l mod 4294967296) = l.
Proof.
  intros l Hl.
  change 16711680 with (Z.shiftl (Z.ones 8) 16). change 65280 with (Z.shiftl (Z.ones 8) 8). change 255 with (Z.shiftl (Z.ones 8) 0).
  change 4294967296 with (2^32). change 72057594037927936 with (2^56). change 18446744073709551616 with (2^64).
  assert (D32 : 0 <= l / 2^32 < 2^30) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (D56 : 0 <= l / 2^56 < 2^6) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (S24 : 0 <= Z.shiftl (l / 2^56) 24 < 2^30) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (Z.mod_small (Z.shiftl (l / 2^56) 24)) by lia.
  set (H := Z.lor _ (Z.land _ (Z.shiftl (Z.ones 8) 0))).
  assert (HB : forall k, 0 <= k -> Z.testbit H k = if k <? 32 then Z.testbit l (k + 32) else false).
  { intros k Hk. unfold H.
    rewrite !Z.lor_spec, !Z.land_spec, !testbit_mask8 by lia.
    rewrite Z.div_pow2_bits by lia.
    destruct (Z.ltb_spec k 24).
    - rewrite (Z.shiftl_spec_low _ 24 k) by lia.
      destruct (Z.ltb_spec k 32); [|lia].
      destruct (Z.testbit l (k + 32)); cbn [andb orb];
        destruct (Z.leb_spec 16 k); destruct (Z.ltb_spec k (16+8)); destruct (Z.leb_spec 8 k); destruct (Z.ltb_spec k (8+8));
        destruct (Z.leb_spec 0 k); destruct (Z.ltb_spec k (0+8)); cbn [andb orb]; try reflexivity; lia.
    - rewrite Z.shiftl_spec, Z.div_pow2_bits by lia. replace (k - 24 + 56) with (k + 32) by lia.
      destruct (Z.leb_spec 16 k); destruct (Z.ltb_spec k (16+8)); destruct (Z.leb_spec 8 k); destruct (Z.ltb_spec k (8+8));
        destruct (Z.leb_spec 0 k); destruct (Z.ltb_spec k (0+8)); try lia; cbn [andb orb].
      rewrite !andb_false_r, !orb_false_r. cbn [orb].
      destruct (Z.ltb_spec k 32); [reflexivity|].
      apply (testbit_small l 62); lia. }
  assert (H0 : 0 <= H).
  { unfold H. repeat (apply Z.lor_nonneg; split); try (apply Z.land_nonneg; left; lia). lia. }
  assert (H32 : H < 2^32).
  { destruct (Z.eq_dec H 0) as [->|NZ]; [lia|].
    destruct (Z.lt_ge_cases H (2^32)) as [X|X]; [exact X|]. exfalso.
    pose proof (Z.bit_log2 H ltac:(lia)) as B. rewrite HB in B by (apply Z.log2_nonneg).
    destruct (Z.ltb_spec (Z.log2 H) 32); [| discriminate B].
    pose proof (Z.log2_le_mono _ _ X) as M. rewrite Z.log2_pow2 in M by lia. lia. }
  rewrite (Z.mod_small (Z.shiftl H 32)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.lor_spec.
  destruct (Z.ltb_spec n 32).
  - rewrite Z.shiftl_spec_low, Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.shiftl_spec, Z.mod_pow2_bits_high, orb_false_r, HB by lia.
    destruct (Z.ltb_spec (n - 32) 32).
    + f_equal. lia.
    + symmetry. apply (testbit_small l 62); lia.
Qed.

(* [comment removed for export] *)
Ltac call_consts_in H := idtac.
Ltac vk_head_of t := lazymatch t with ?f _ => vk_head_of f | _ => t end.
Ltac post_call_fr segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  (let T := type of PO in let h := vk_head_of T in try unfold h in PO);
  call_consts_in PO;
  rewrite ?unsigned_lit in PO by lia;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Tactic Notation "call_fr" uconstr(SPEC) "by" tactic3(side) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC; side | post_call_fr segs m ]
  end.

(* [comment removed for export] *)
Definition kept (P : Prop) : Prop := P.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hide H := (lazymatch type of H with ?T__ => change (kept T__) in H end).
Ltac unhide H := (lazymatch type of H with kept ?T__ => change T__ in H | _ => idtac end).
(* [comment removed for export] *)
Ltac hide_neqs := repeat match goal with H : (?x <> ?y) |- _ => hide H end.
Ltac unhide_neqs := repeat match goal with H : kept (?x <> ?y) |- _ => unhide H end.
(* [comment removed for export] *)
Ltac hide_mods := repeat match goal with H : (?x mod ?y = ?z)%Z |- _ => hide H end.
Ltac unhide_mods := repeat match goal with H : kept (?x mod ?y = ?z)%Z |- _ => unhide H end.
Ltac hide_slow := hide_neqs; hide_mods.
Ltac unhide_slow := unhide_neqs; unhide_mods.

Section S.
  Context {Clg : Ceiling} (L : AllocLayout) {AI : AllocSpec L}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma vsb_obj_munch : forall (A : AS) (W : list ivl) (m m' : mem) (S : Z) (v : vsb_rec) (fin : bool),
    vsb_obj L A m S v fin -> munch W m m' -> wmono (al_segs L) m m' ->
    disjoint_from W S 40 -> disjoint_from W (vb_buf v) (vb_size v) ->
    vsb_obj L A m' S v fin.
  Proof.
    (intros A W m m' S v fin; (first [ intro dR_2; dand6 dR_2 as VC VI LS LB NE (bs & U8 & LBS & NUL) | intros (VC & VI & LS & LB & NE & (bs & U8 & LBS & NUL)) ]); intros MU WM D1 D2).
    split; [| split; [exact VI| split; [exact LS| split; [exact LB| split; [exact NE|]]]]].
    - eapply rw_cells_transport; [exact VC| exact MU| exact WM|]. rewrite vsb_cells_size. exact D1.
    - exists bs. split; [| split; [exact LBS| exact NUL]].
      eapply u8arr_transport; [exact U8| exact MU| exact WM|]. rewrite LBS. exact D2.
  Qed.

  (* [comment removed for export] *)
  Lemma blk_avoids_crange : forall (A A' : AS) (m0 m' : mem) (xsp win : Z) (V : Z -> Prop) (nb nsz a n : Z),
    cframe L (owned A) (owned A') xsp win V (blk nb nsz) m0 m' ->
    crange A m0 a n -> 0 < n -> a + n <= xsp - win -> nb <> 0 -> 0 < nsz ->
    (forall x, a <= x < a + n -> ~ V x) ->
    ~ (nb < a + n /\ a < nb + nsz).
  Proof.
    (intros A A' m0 m' xsp win V nb nsz a n; (first [ intro dR_3; dand3 dR_3 as C1 C2 C3 | intros (C1 & C2 & C3) ]); (first [ intro dR_4; dand3 dR_4 as Ha Hn CR | intros (Ha & Hn & CR) ]); intros N0 BW NB NS NV [X Y]).
    set (x := Z.max a nb).
    (first [ pose proof ((CR (x - a) ltac:(lia))) as dR_1; dand3 dR_1 as NO NE VIS | destruct (CR (x - a) ltac:(lia)) as (NO & NE & VIS) ]). replace (a + (x - a)) with x in NO, NE, VIS by lia.
    destruct (C3 x ltac:(lia) ltac:(lia) NE ltac:(unfold blk; lia)) as [O | [HV | [MN NI]]].
    - exact (NO O).
    - exact (NV x ltac:(lia) HV).
    - destruct VIS as [VIS|VIS]; [exact (VIS MN)| exact (NI VIS)].
  Qed.
End S.
End V_VepKit.


(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive vstate : Type :=
  S_Start | S_BOM | S_TestXml | S_NotXml | S_NotMyTag | S_NxtTag | S_StartTag | S_Comment | S_CommentESI
| S_CDATA | S_end_ESITag | S_ESITag | S_ESI_Include | S_ESI_Remove | S_ESI_Comment | S_ESI_Bogon
| S_InTag | S_TagError | S_Attr | S_SkipAttribute | S_AttrGetValue | S_AttrDelim | S_AttrValue
| S_Until | S_Match | S_MatchBuf.

Record vimg : Type := VIMG {
  vi_bss        : Z;   (* [comment removed for export] *)
  vi_cb         : Z;   (* [comment removed for export] *)
  vi_do_include : Z;
  vi_do_remove  : Z;
  vi_do_comment : Z;
  vi_st         : vstate -> Z;   (* [comment removed for export] *)
  vi_url        : Z;   (* [comment removed for export] *)
  vi_empty      : Z;   (* [comment removed for export] *)
  vi_arrow      : Z;   (* [comment removed for export] *)
  vi_cdata_end  : Z;   (* [comment removed for export] *)
  vi_tbl_bom : Z; vi_tbl_starttag : Z; vi_tbl_esi : Z; vi_tbl_attr_include : Z
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record henv : Type := HENV {
  h_sp  : Z;    (* [comment removed for export] *)
  h_bss : Z     (* [comment removed for export] *)
}.
Definition h_wsbuf  (H : henv) : Z := h_sp H + 16.
Definition h_hd     (H : henv) : Z := h_sp H + 1040.
Definition h_vsbloc (H : henv) : Z := h_sp H + 1072.
Definition h_ws     (H : henv) : Z := h_sp H + 1080.
Definition h_wrk    (H : henv) : Z := h_sp H + 1120.
Definition h_vc     (H : henv) : Z := h_sp H + 1304.
Definition h_resp   (H : henv) : Z := h_sp H + 1376.
Definition h_req    (H : henv) : Z := h_sp H + 1432.
Definition h_cp     (H : henv) : Z := h_sp H + 1488.
Definition h_vsc    (H : henv) : Z := h_sp H + 2240.
(* [comment removed for export] *)
Definition HFRAME : Z := 3664.

(* [comment removed for export] *)
Definition http_cells (hd : Z) (mid : list byte) (ws : Z) (tl : list byte) (pad : list byte) : list cell :=
  [ C4 (Z_to_bv 64 HTTP_MAGIC); CB 4 pad; C8 (Z_to_bv 64 hd); CB 24 mid; C8 (Z_to_bv 64 ws); CB 8 tl ].

Section World.
  Context {Clg : Ceiling} (L : AllocLayout) {AI : AllocSpec L}.   (* [comment removed for export] *)
  Let segs := al_segs L.

  (* [comment removed for export] *)
  Definition henv_geom (H : henv) : Prop :=
    h_sp H mod 16 = 0 /\ alloc_ceiling + 12720 <= h_sp H /\ h_sp H + HFRAME + 64 <= 2^47.

  (* [comment removed for export] *)
  Definition glob_ok (V : vimg) (H : henv) (m : mem) : Prop :=
       h_bss H = vi_bss V
    /\ rw_cells segs m (h_bss H) [C8 (Z_to_bv 64 (h_vsc H)); C8 (Z_to_bv 64 (h_cp H))]
    /\ rw_cells segs m (h_cp H) [CB 752 (repeat (Z_to_bv 8 0) 752)]
    /\ (exists bs, rw_cells segs m (h_vsc H + 1304) [CB 16 bs]).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition hobj_ok (V : vimg) (H : henv) (m : mem) : Prop :=
       (exists pad rest, length pad = 12%nat /\ length rest = 40%nat /\
          rw_cells segs m (h_vc H) (vc_cells pad (h_resp H) (h_wrk H) rest))
    /\ (exists pad rest, length pad = 28%nat /\ length rest = 144%nat /\ rw_cells segs m (h_wrk H) (wrk_cells pad rest))
    /\ (exists mid tl pad, length mid = 24%nat /\ length tl = 8%nat /\ length pad = 4%nat /\
          rw_cells segs m (h_req H) (http_cells (h_hd H) mid (h_ws H) tl pad))
    /\ (exists hd mid tl pad, length mid = 24%nat /\ length tl = 8%nat /\ length pad = 4%nat /\
          rw_cells segs m (h_resp H) (http_cells hd mid (h_ws H) tl pad))
    /\ rw_cells segs m (h_hd H + 16) [C8 (Z_to_bv 64 (vi_url V))].

  Definition henv_ok (V : vimg) (H : henv) (m : mem) : Prop := glob_ok V H m /\ hobj_ok V H m.

  (* [comment removed for export] *)
  Definition ws_id_req : list byte := [Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0].   (* [comment removed for export] *)
  Definition ws_id_Req : list byte := [Z_to_bv 8 82; Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0].    (* [comment removed for export] *)
  Definition ws_id_ok (id : list byte) : Prop := id = ws_id_req \/ id = ws_id_Req.

  Definition ws_rec_of (H : henv) (id : list byte) : ws_rec := WSR id (h_wsbuf H) 0 0 (h_wsbuf H + 1016).

  Definition ws0_obj (H : henv) (m : mem) : Prop :=
    exists id, ws_id_ok id /\
      rw_cells segs m (h_ws H) (ws_cells (ws_rec_of H id)) /\
      rw_cells segs m (h_wsbuf H) (wsemu_cells (wsemu_WS0 (h_wsbuf H))).

  Definition ws1_obj (H : henv) (A : AS) (m : mem) (wa vep : Z) : Prop :=
    exists id pad, ws_id_ok id /\ length pad = 4%nat /\
      rw_cells segs m (h_ws H) (ws_cells (ws_rec_of H id)) /\
      rw_cells segs m (h_wsbuf H) (wsemu_cells (wsemu_WS1 wa)) /\
      a_live A wa = Some 40 /\ rw_cells segs m wa (wsalloc_cells (wsalloc_WS1 (h_wsbuf H) vep) pad) /\
      a_live A vep = Some 312.

  (* [comment removed for export] *)
  Definition vep_obj (A : AS) (m : mem) (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) : Prop :=
    a_live A VEP = Some 312 /\ rw_cells segs m VEP (vep_cells v tag q) /\ length tag = 8%nat /\ vep_pads_wf q.

  (* [comment removed for export] *)
  Definition data_obj (A : AS) (m : mem) (DATA : Z) (inp : list byte) : Prop :=
    a_live A DATA = Some (Z.of_nat (length inp)) /\ bytes_at segs m DATA inp /\ 1 <= Z.of_nat (length inp) < 2^26.

End World.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Transport.
  Context {Clg : Ceiling} (L : AllocLayout) {AI : AllocSpec L}.   (* [comment removed for export] *)
  Let segs := al_segs L.

  Lemma rw_cells_munch : forall W m m' A cs,
    rw_cells segs m A cs -> munch W m m' -> wmono segs m m' ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> outside W a) ->
    rw_cells segs m' A cs.
  Proof.
    intros W m m' A cs RC MU WM OUT.
    destruct RC as [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
    - (first [ dand3 HB as B0 B1 B | destruct HB as (B0 & B1 & B) ]). split; [exact B0|]. split; [exact B1|]. intros i Hi.
      unfold mrd. rewrite MU; [apply B; exact Hi|]. rewrite wa_unsigned by lia. apply OUT.
      rewrite cells_bytes_length in Hi by exact Hwf. lia.
    - eapply wr_at_transport; eauto.
  Qed.

  Lemma glob_ok_munch : forall V H W m m',
    glob_ok L V H m -> munch W m m' -> wmono segs m m' ->
    (forall a, (h_bss H <= a < h_bss H + 16 \/ h_cp H <= a < h_cp H + 752 \/ h_vsc H + 1304 <= a < h_vsc H + 1320) ->
               outside W a) ->
    glob_ok L V H m'.
  Proof.
    (intros V H W m m'; (first [ intro dR_14; dand4 dR_14 as E B C [bs D] | intros (E & B & C & [bs D]) ]); intros MU WM OUT).
    split; [exact E|]. split; [|split; [|exists bs]];
      (eapply rw_cells_munch; [eassumption| exact MU| exact WM|]); intros a Ha; apply OUT; cbn in Ha; lia.
  Qed.

  Lemma hobj_ok_munch : forall V H W m m',
    hobj_ok L V H m -> munch W m m' -> wmono segs m m' ->
    (forall a, (h_vc H <= a < h_vc H + 72 \/ h_wrk H <= a < h_wrk H + 184 \/ h_req H <= a < h_req H + 56 \/
                h_resp H <= a < h_resp H + 56 \/ h_hd H + 16 <= a < h_hd H + 24) -> outside W a) ->
    hobj_ok L V H m'.
  Proof.
    (intros V H W m m'; (first [ intro dR_15; dand5 dR_15 as VC WK RQ RS HD | intros (VC & WK & RQ & RS & HD) ]); intros MU WM OUT).
    (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]). (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]).
    (first [ dex3 RQ as mi1 tl1 pd1; dand4 RQ as L5 L6 L7 RQ | dand7 RQ as mi1 tl1 pd1 L5 L6 L7 RQ | destruct RQ as (mi1 & tl1 & pd1 & L5 & L6 & L7 & RQ) ]). (first [ dex4 RS as hd2 mi2 tl2 pd2; dand4 RS as L8 L9 L10 RS | dand8 RS as hd2 mi2 tl2 pd2 L8 L9 L10 RS | destruct RS as (hd2 & mi2 & tl2 & pd2 & L8 & L9 & L10 & RS) ]).
    split; [exists p1, r1; split; [exact L1|]; split; [exact L2|]|].
    2: split; [exists p2, r2; split; [exact L3|]; split; [exact L4|]|].
    3: split; [exists mi1, tl1, pd1; split; [exact L5|]; split; [exact L6|]; split; [exact L7|]|].
    4: split; [exists hd2, mi2, tl2, pd2; split; [exact L8|]; split; [exact L9|]; split; [exact L10|]|].
    all: eapply rw_cells_munch; [eassumption| exact MU| exact WM|]; intros a Ha; apply OUT;
         cbn [cells_size csize vc_cells wrk_cells http_cells Nat.add length] in Ha; lia.
  Qed.

  Lemma henv_ok_munch : forall V H W m m',
    henv_ok L V H m -> munch W m m' -> wmono segs m m' ->
    (forall a, (h_bss H <= a < h_bss H + 16 \/ h_hd H + 16 <= a < h_hd H + 24 \/ h_wrk H <= a < h_req H + 56 + 752 \/
                h_vsc H + 1304 <= a < h_vsc H + 1320) -> outside W a) ->
    henv_ok L V H m'.
  Proof.
    intros V H W m m' [G O] MU WM OUT. split.
    - eapply glob_ok_munch; [exact G| exact MU| exact WM|]. intros a Ha. apply OUT.
      unfold h_cp, h_vsc, h_wrk, h_req in *. lia.
    - eapply hobj_ok_munch; [exact O| exact MU| exact WM|]. intros a Ha. apply OUT.
      unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_cp in *. lia.
  Qed.

  Lemma ws0_obj_munch : forall H W m m',
    ws0_obj L H m -> munch W m m' -> wmono segs m m' ->
    (forall a, (h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32) -> outside W a) ->
    ws0_obj L H m'.
  Proof.
    (intros H W m m'; (first [ intro dR_16; dex1 dR_16 as id; dand3 dR_16 as ID A1 A2 | intro dR_16; dand4 dR_16 as id ID A1 A2 | intros (id & ID & A1 & A2) ]); intros MU WM OUT). exists id. split; [exact ID|].
    pose proof ID as ID'. destruct ID' as [-> | ->];
    (split; (eapply rw_cells_munch; [eassumption| exact MU| exact WM|]); intros a Ha; apply OUT; cbn in Ha; lia).
  Qed.

  Lemma ws1_obj_munch : forall H A W m m' wa vep,
    ws1_obj L H A m wa vep -> munch W m m' -> wmono segs m m' ->
    (forall a, (h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32 \/ wa <= a < wa + 40) -> outside W a) ->
    ws1_obj L H A m' wa vep.
  Proof.
    (intros H A W m m' wa vep; (first [ intro dR_17; dex2 dR_17 as id pad; dand7 dR_17 as ID LP A1 A2 LV A3 LV2 | intro dR_17; dand9 dR_17 as id pad ID LP A1 A2 LV A3 LV2 | intros (id & pad & ID & LP & A1 & A2 & LV & A3 & LV2) ]); intros MU WM OUT). exists id, pad.
    split; [exact ID|]. split; [exact LP|].
    pose proof ID as ID'. destruct ID' as [-> | ->];
    (split; [|split; [|split; [exact LV| split; [|exact LV2]]]];
     (eapply rw_cells_munch; [eassumption| exact MU| exact WM|]); intros a Ha; apply OUT; cbn in Ha; lia).
  Qed.
End Transport.

(* [comment removed for export] *)
Section Intro.
  Context {Clg : Ceiling} (L : AllocLayout) {AI : AllocSpec L}.   (* [comment removed for export] *)
  Let segs := al_segs L.

  Lemma hobj_ok_intro : forall V H m p1 r1 p2 r2 mi1 tl1 pd1 hd2 mi2 tl2 pd2,
    length p1 = 12%nat -> length r1 = 40%nat -> rw_cells segs m (h_vc H) (vc_cells p1 (h_resp H) (h_wrk H) r1) ->
    length p2 = 28%nat -> length r2 = 144%nat -> rw_cells segs m (h_wrk H) (wrk_cells p2 r2) ->
    length mi1 = 24%nat -> length tl1 = 8%nat -> length pd1 = 4%nat ->
    rw_cells segs m (h_req H) (http_cells (h_hd H) mi1 (h_ws H) tl1 pd1) ->
    length mi2 = 24%nat -> length tl2 = 8%nat -> length pd2 = 4%nat ->
    rw_cells segs m (h_resp H) (http_cells hd2 mi2 (h_ws H) tl2 pd2) ->
    rw_cells segs m (h_hd H + 16) [C8 (Z_to_bv 64 (vi_url V))] ->
    hobj_ok L V H m.
  Proof.
    intros. split; [eexists _, _; eauto|]. split; [eexists _, _; eauto|].
    split; [eexists _, _, _; eauto|]. split; [eexists _, _, _, _; eauto| assumption].
  Qed.

  Lemma glob_ok_intro : forall V H m bs,
    h_bss H = vi_bss V ->
    rw_cells segs m (h_bss H) [C8 (Z_to_bv 64 (h_vsc H)); C8 (Z_to_bv 64 (h_cp H))] ->
    rw_cells segs m (h_cp H) [CB 752 (repeat (Z_to_bv 8 0) 752)] ->
    rw_cells segs m (h_vsc H + 1304) [CB 16 bs] ->
    glob_ok L V H m.
  Proof. intros. split; [assumption|]. split; [assumption|]. split; [assumption| eexists; eassumption]. Qed.

  Lemma ws0_obj_intro : forall H m id,
    ws_id_ok id ->
    rw_cells segs m (h_ws H) (ws_cells (ws_rec_of H id)) ->
    rw_cells segs m (h_wsbuf H) (wsemu_cells (wsemu_WS0 (h_wsbuf H))) ->
    ws0_obj L H m.
  Proof. intros. eexists; eauto. Qed.

  Lemma ws1_obj_intro : forall H A m wa vep id pad,
    ws_id_ok id -> length pad = 4%nat ->
    rw_cells segs m (h_ws H) (ws_cells (ws_rec_of H id)) ->
    rw_cells segs m (h_wsbuf H) (wsemu_cells (wsemu_WS1 wa)) ->
    a_live A wa = Some 40 -> rw_cells segs m wa (wsalloc_cells (wsalloc_WS1 (h_wsbuf H) vep) pad) ->
    a_live A vep = Some 312 ->
    ws1_obj L H A m wa vep.
  Proof.
    intros H A m wa vep id pad ID LP A1 A2 LV A3 LV2. exists id, pad.
    split; [exact ID|]. split; [exact LP|]. split; [exact A1|]. split; [exact A2|]. split; [exact LV|]. split; [exact A3| exact LV2].
  Qed.
End Intro.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TransportCall.
  Context {Clg : Ceiling} (L : AllocLayout) {AI : AllocSpec L}.   (* [comment removed for export] *)
  Let segs := al_segs L.

  (* [comment removed for export] *)
  Lemma rw_cells_ccall_stack : forall A A' m md m' sp win V N a cs,
    ainv A m md -> cframe L (owned A) (owned A') sp win V N m m' ->
    rw_cells segs m a cs -> alloc_ceiling <= a ->
    (a + Z.of_nat (cells_size cs) <= sp - win \/ sp <= a) ->
    (forall x, a <= x < a + Z.of_nat (cells_size cs) -> ~ V x) ->
    rw_cells segs m' a cs.
  Proof.
    intros A A' m md m' sp win V N a cs AI0 CF RC CE W NV.
    pose proof (rw_cells_bound _ _ _ _ RC) as B.
    eapply (rw_cells_ccall L A A' sp win V N m m' CF); [| | exact RC].
    - eapply crange_stack; [exact AI0| exact CE| lia|]. apply (rw_cells_mapped L _ _ _ RC). apply (off_image_stack L). exact CE.
    - split; [exact W|]. intros i Hi. apply NV. lia.
  Qed.

  #[using="segs"] Lemma hobj_ok_ccall : forall V H A A' m md m' sp win Vc N,
    ainv A m md -> cframe L (owned A) (owned A') sp win Vc N m m' -> henv_geom H ->
    hobj_ok L V H m -> sp <= h_sp H ->
    (forall a, (h_vc H <= a < h_vc H + 72 \/ h_wrk H <= a < h_wrk H + 184 \/ h_req H <= a < h_req H + 56 \/
                h_resp H <= a < h_resp H + 56 \/ h_hd H + 16 <= a < h_hd H + 24) -> ~ Vc a) ->
    hobj_ok L V H m'.
  Proof.
    (intros V H A A' m md m' sp win Vc N AI0 CF; (first [ intro dR_18; dand3 dR_18 as G1 G2 G3 | intros (G1 & G2 & G3) ]); (first [ intro dR_19; dand5 dR_19 as VC WK RQ RS HD | intros (VC & WK & RQ & RS & HD) ]); intros SP NV).
    unfold h_vc, h_wrk, h_req, h_resp, h_hd in *.
    (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]). (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]).
    (first [ dex3 RQ as mi1 tl1 pd1; dand4 RQ as L5 L6 L7 RQ | dand7 RQ as mi1 tl1 pd1 L5 L6 L7 RQ | destruct RQ as (mi1 & tl1 & pd1 & L5 & L6 & L7 & RQ) ]). (first [ dex4 RS as hd2 mi2 tl2 pd2; dand4 RS as L8 L9 L10 RS | dand8 RS as hd2 mi2 tl2 pd2 L8 L9 L10 RS | destruct RS as (hd2 & mi2 & tl2 & pd2 & L8 & L9 & L10 & RS) ]).
    pose proof (rw_cells_bound _ _ _ _ VC) as B1. pose proof (rw_cells_bound _ _ _ _ WK) as B2.
    pose proof (rw_cells_bound _ _ _ _ RQ) as B3. pose proof (rw_cells_bound _ _ _ _ RS) as B4.
    cbn [cells_size csize vc_cells wrk_cells http_cells Nat.add length] in B1, B2, B3, B4.
    split; [exists p1, r1; split; [exact L1|]; split; [exact L2|]|].
    2: split; [exists p2, r2; split; [exact L3|]; split; [exact L4|]|].
    3: split; [exists mi1, tl1, pd1; split; [exact L5|]; split; [exact L6|]; split; [exact L7|]|].
    4: split; [exists hd2, mi2, tl2, pd2; split; [exact L8|]; split; [exact L9|]; split; [exact L10|]|].
    all: eapply (rw_cells_ccall_stack A A' m md m' sp win Vc N); [exact AI0| exact CF| eassumption| | |];
         unfold h_vc, h_wrk, h_req, h_resp, h_hd; cbn [cells_size csize vc_cells wrk_cells http_cells Nat.add length];
         [lia| lia|]; intros x Hx; apply NV; lia.
  Qed.

  #[using="segs"] Lemma glob_ok_ccall : forall V H A A' m md m' sp win Vc N,
    ainv A m md -> cframe L (owned A) (owned A') sp win Vc N m m' -> henv_geom H ->
    glob_ok L V H m -> sp <= h_sp H -> alloc_ceiling <= sp - win ->
    (* [comment removed for export] *)
    al_rw_lo L <= h_bss H -> h_bss H + 16 <= al_image_hi L ->
    (forall i, 0 <= i < 16 -> ~ al_static L (h_bss H + i)) -> (h_bss H + 16 <= al_errno L \/ al_errno L + 4 <= h_bss H) ->
    (forall a, (h_bss H <= a < h_bss H + 16 \/ h_cp H <= a < h_cp H + 752 \/ h_vsc H + 1304 <= a < h_vsc H + 1320) -> ~ Vc a) ->
    glob_ok L V H m'.
  Proof.
    (intros V H A A' m md m' sp win Vc N AI0 CF; (first [ intro dR_20; dand3 dR_20 as G1 G2 G3 | intros (G1 & G2 & G3) ]); intros GL SP CE R1 R2 R3 R4 NV).
    unfold glob_ok in *. unfold h_cp, h_vsc in *. (first [ dand4 GL as E B C [bs D] | destruct GL as (E & B & C & [bs D]) ]).
    pose proof (as_layout_order (L:=L)) as LAY. pose proof alloc_ceiling_val as ACV.
    split; [exact E|]. split; [|split; [|exists bs]].
    - eapply (rw_cells_ccall L A A' sp win Vc N m m' CF); [| | exact B].
      + eapply crange_data; [exact AI0| exact R1| cbn; exact R2| cbn; lia| cbn; exact R3| cbn; exact R4].
      + split; [cbn; lia|]. intros i Hi. apply NV. cbn in Hi. lia.
    - eapply (rw_cells_ccall_stack A A' m md m' sp win Vc N); [exact AI0| exact CF| exact C| lia| cbn; lia|].
      intros x Hx. apply NV. cbn in Hx. lia.
    - eapply (rw_cells_ccall_stack A A' m md m' sp win Vc N); [exact AI0| exact CF| exact D| lia| cbn; lia|].
      intros x Hx. apply NV. cbn in Hx. lia.
  Qed.

  (* [comment removed for export] *)

  #[using="segs"] Lemma ws1_obj_ccall : forall H A A' m md m' sp win Vc N wa vep,
    ainv A m md -> cframe L (owned A) (owned A') sp win Vc N m m' -> henv_geom H ->
    ws1_obj L H A m wa vep -> sp <= h_sp H -> alloc_ceiling <= sp - win ->
    a_live A' wa = Some 40 -> a_live A' vep = Some 312 ->
    (forall a, (h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32 \/ wa <= a < wa + 40) -> ~ Vc a) ->
    ws1_obj L H A' m' wa vep.
  Proof.
    (intros H A A' m md m' sp win Vc N wa vep AI0 CF; (first [ intro dR_22; dand3 dR_22 as G1 G2 G3 | intros (G1 & G2 & G3) ]); intros WS SP CE LV' LV2' NV).
    unfold ws1_obj in *. unfold h_ws, h_wsbuf in *. (first [ dex2 WS as id pad; dand7 WS as ID LP A1 A2 LV A3 LV2 | dand9 WS as id pad ID LP A1 A2 LV A3 LV2 | destruct WS as (id & pad & ID & LP & A1 & A2 & LV & A3 & LV2) ]).
    exists id, pad. split; [exact ID|]. split; [exact LP|].
    (first [ pose proof ((live_geom L A m md wa 40 AI0 LV)) as dR_13; dand7 dR_13 as _ _ W1 W2 _ _ _ | destruct (live_geom L A m md wa 40 AI0 LV) as (_ & _ & W1 & W2 & _ & _ & _) ]).
    pose proof ID as ID'. destruct ID' as [-> | ->].
    all: split; [|split; [|split; [exact LV'| split; [|exact LV2']]]].
    1,2,4,5: eapply (rw_cells_ccall_stack A A' m md m' sp win Vc N); [exact AI0| exact CF| eassumption| lia| cbn; lia|];
         intros x Hx; apply NV; cbn in Hx; lia.
    all: eapply (rw_cells_ccall L A A' sp win Vc N m m' CF); [| | exact A3];
         [ eapply crange_block; [exact AI0| exact LV| lia| cbn; lia| cbn; lia]
         | split; [cbn; lia|]; intros i Hi; apply NV; cbn in Hi; lia ].
  Qed.
End TransportCall.
