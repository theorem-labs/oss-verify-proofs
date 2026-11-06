(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths changed; 255 of its 299 lines of code are new or changed and 107 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/Prog/fuzz_catalogue_row.v, with its module names changed; 601 of its 675 lines of code are new or changed and 225 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/Prog/reac_box_pin_parse.v, with its module paths changed; 1369 of its 1406 lines of code are new or changed and 638 lines of the source are left out. *)
(* reac_served_mark (reac_served_mark.c:48-92), PLAIN build: the walk of its contract
   (lib/Prog/reac_served_mark_c.v) on the plain image, 0x16470..0x1663c. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c printf_facts_c
  mk_leaf mk_leaf_fp mk_call mk_str mk_marks link_msgs_fit reac_served_mark_c reac_served_mark_aux
  reac_link_alias_read_c reac_link_alias_write_c remember_c reac_code_emit_c fprintf_c vfprintf_c
  bcmp_c model_decide_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require model_decide bcmp.
Local Open Scope Z_scope.

(* the contract's three parts, by name *)
Definition mk_pre (sink : Z) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs m => exists kbs tab nm k,
       nlk_at m kbs /\ frame_apart_gnl regs 17248 /\ nlk_wf kbs /\ nk_open kbs = 0
       /\ nk_opened kbs + 2 < 2 ^ 31 /\ nk_closed kbs + 2 < 2 ^ 31 /\ iftab_at m kbs tab
       /\ mark_errno_ok m regs 17248 sink /\ mark_table_ok m regs 17248 sink tab /\ policy_ro m
       /\ u64_at m A_G_SAY sink /\ sink <> 0
       /\ memfile_k m sink k /\ k + MARK_LINE_MAX <= MemFile.MF_BUFSIZ
       /\ sink + FILE_BLOCK <= spZ regs - 17248
       /\ str_arg m (arg regs 1) nm /\ mark_name_ok m regs 17248 sink nm
       /\ mark_block_ok m regs 17248 sink.

Definition mk_wr (sink : Z) : bvmap 5 word -> (word -> option byte) -> list ivl :=
  fun regs m => [(A_G_NL, A_G_NL + NK_N_SENT + 4);
                 (errno_at regs, errno_at regs + 4);
                 (arg regs 0, arg regs 0 + (if arg regs 0 =? 0 then 0 else MK_SIZE));
                 mf_block sink].

Definition post_file (sink : Z) (m m' : word -> option byte) : Prop :=
  forall k, memfile_k m sink k -> exists k', k <= k' <= k + MARK_LINE_MAX /\ memfile_k m' sink k'.

Definition post_marks (A0 A1 : Z) (m : word -> option byte) (r : word) (m' : word -> option byte) : Prop :=
  forall kbs tab nm gbs,
    nlk_at m kbs -> iftab_at m kbs tab -> str_arg m A1 nm -> marks_at m A0 gbs ->
    let M := mark_lib tab nm (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) in
    r = wz (m_rc M)
    /\ (exists gbs', marks_at m' A0 gbs' /\ marks_wf gbs'
          /\ mk_names gbs' = m_marks M
          /\ mk_n gbs' = Z.of_nat (length (m_marks M)))
    /\ (exists kbs', nlk_at m' kbs' /\ nlk_wf kbs'
          /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
          /\ nk_n_if kbs' = nk_n_if kbs /\ iftab_at m' kbs' tab
          /\ nk_next kbs' = Z.of_nat (k_next (m_state M))
          /\ nk_sent kbs' = m_reqs M /\ nk_n_sent kbs' = Z.of_nat (length (m_reqs M))
          /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
          /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
          /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 2).

Definition mk_post (sink : Z) :
    bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs m regs' m' =>
       post_file sink m m'
       /\ (arg regs 0 = 0 -> getr regs' 10 = wz (- E_INVAL)
             /\ forall kbs, nlk_at m kbs -> nlk_at m' kbs)
       /\ (arg regs 0 <> 0 -> post_marks (arg regs 0) (arg regs 1) m (getr regs' 10) m').

(* the three refusals that return -EINVAL with nothing changed but the frame *)
Lemma marks_refused : forall m m1 A0 A1 kbs tab,
  nlk_at m kbs -> nlk_wf kbs -> nk_open kbs = 0 -> iftab_at m kbs tab ->
  (exists gbs, marks_at m A0 gbs /\ marks_wf gbs) ->
  (forall kbs0, nlk_at m kbs0 -> nlk_at m1 kbs0) ->
  (forall tab0, iftab_at m kbs tab0 -> iftab_at m1 kbs tab0) ->
  (forall gbs, marks_at m A0 gbs -> marks_at m1 A0 gbs) ->
  (forall nm0, str_arg m A1 nm0 -> nm0 = None \/ nm0 = Some []) ->
  post_marks A0 A1 m (wz (- E_INVAL)) m1.
Proof.
  intros m m1 A0 A1 kbs tab NL WF OP TB (g & G & GW) HN HT HG HS kbs0 tab0 nm0 gbs N0 T0 S0 G0.
  pose proof (nlk_unique _ _ _ N0 NL) as E. subst kbs0.
  pose proof (marks_unique _ _ _ _ G0 G) as E. subst gbs.
  assert (Hm : mark_lib tab0 nm0 (mk_names g) (nk_sent kbs) (nk_kstate kbs)
               = Mres (- E_INVAL) (mk_names g) (nk_sent kbs) (nk_kstate kbs))
    by (destruct (HS nm0 S0) as [-> | ->]; reflexivity).
  cbv zeta. rewrite Hm. cbn [m_rc m_marks m_reqs m_state].
  split; [reflexivity|]. split.
  - exists g. split; [exact (HG g G)|]. split; [exact GW|]. split; [reflexivity|]. exact (mk_n_names g GW).
  - exists kbs. split; [exact (HN kbs NL)|]. split; [exact WF|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact (HT tab0 T0)|]. split; [exact (nk_next_kstate kbs WF)|].
    split; [reflexivity|]. split; [exact (nk_sent_length kbs WF)|].
    split; [exact OP|]. split; [reflexivity|]. split; [reflexivity|]. lia.
Qed.

(* the answer of every path that reaches a call, from the final kernel and marks *)
Lemma post_marks_of : forall m mc A0 A1 kbs tab nm gbs (r : word) (M : mres) kbsc gbsc,
  nlk_at m kbs -> iftab_at m kbs tab -> str_arg m A1 nm -> marks_at m A0 gbs ->
  mark_lib tab nm (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) = M ->
  r = wz (m_rc M) ->
  marks_at mc A0 gbsc -> marks_wf gbsc -> mk_names gbsc = m_marks M ->
  nlk_at mc kbsc -> nlk_wf kbsc -> nk_chunks kbsc = nk_chunks kbs -> nk_end_errno kbsc = nk_end_errno kbs ->
  nk_n_if kbsc = nk_n_if kbs -> iftab_at mc kbsc tab -> nk_next kbsc = Z.of_nat (k_next (m_state M)) ->
  nk_sent kbsc = m_reqs M -> nk_n_sent kbsc = Z.of_nat (length (m_reqs M)) -> nk_open kbsc = 0 ->
  nk_misuse kbsc = nk_misuse kbs -> nk_opened kbsc - nk_closed kbsc = nk_opened kbs - nk_closed kbs ->
  nk_opened kbs <= nk_opened kbsc <= nk_opened kbs + 2 ->
  post_marks A0 A1 m r mc.
Proof.
  intros m mc A0 A1 kbs tab nm gbs r M kbsc gbsc NL TB SA GB HM HR GC GW GN NC WC E1 E2 E3 TC E4 E5 E6 E7
    E8 E9 E10 kbs0 tab0 nm0 gbs0 N0 T0 S0 G0.
  pose proof (nlk_unique _ _ _ N0 NL) as E. subst kbs0.
  pose proof (iftab_unique _ _ _ _ T0 TB) as E. subst tab0.
  pose proof (str_arg_unique _ _ _ _ S0 SA) as E. subst nm0.
  pose proof (marks_unique _ _ _ _ G0 GB) as E. subst gbs0.
  cbv zeta. rewrite HM.
  split; [exact HR|]. split.
  - exists gbsc. split; [exact GC|]. split; [exact GW|]. split; [exact GN|].
    rewrite <- GN. exact (mk_n_names gbsc GW).
  - exists kbsc. repeat (split; [assumption|]). exact E10.
Qed.

(* mark_core on a non-empty name, the buffers' caps as the code passes them *)
Lemma mark_lib_some : forall tab x s marks reqs K,
  mark_lib tab (Some (x :: s)) marks reqs K =
  let r := read_core tab (Some (x :: s)) 32 256 reqs K in
  if negb (r_rc r =? 0) then Mres (r_rc r) marks (r_reqs r) (r_state r)
  else
    let v := decide (Some (r_kind r)) (Some (r_alias r)) in
    if v =? V_MARK then
      let w := write_core tab (Some (x :: s)) (Some link_spec.S_SERVED) (r_reqs r) (r_state r) in
      if negb (w_rc w =? 0) then Mres (w_rc w) marks (w_reqs w) (w_state w)
      else Mres v (remember marks (x :: s)) (w_reqs w) (w_state w)
    else if (v =? V_OURS) && bl_eqb (r_alias r) link_spec.S_SERVED
         then Mres v (remember marks (x :: s)) (r_reqs r) (r_state r)
         else Mres v marks (r_reqs r) (r_state r).
Proof. reflexivity. Qed.

(* a callee Post reads registers only through getr *)
Ltac post_ext_tac :=
  let r1 := fresh "r1" in let r2 := fresh "r2" in let mm := fresh "mm" in let q1 := fresh "q1" in
  let q2 := fresh "q2" in let mm' := fresh "mm'" in let E1 := fresh "E1" in let E2 := fresh "E2" in
  let H := fresh "H" in
  intros r1 r2 mm q1 q2 mm' E1 E2 H; unfold emit_fmt in *; unfold arg, res, spZ, errno_at in *;
  repeat rewrite <- E1; repeat rewrite <- E2; exact H.

(* ==========================================================================
   The Pres of the printing calls: reac_code_emit at 0x164ec and 0x16638, fprintf at 0x16598
   and 0x165f8. The register map is abstract; the walk passes facts about `getr regs i`, which
   compute to the words of its concrete map.
   ========================================================================== *)

Definition ce_pre := ltac:(let t := eval cbv delta [reac_code_emit_contract] in reac_code_emit_contract in
  match t with leaf_fp _ _ ?P _ _ => exact P end).

(* the interface name as the %s of a callee whose window is [lo, sp) *)
Definition name_ok (m : word -> option byte) (r : word) (name : list byte) (Sp lo f : Z) : Prop :=
  cstr_at m (bv_unsigned r) name /\ bv_unsigned r <> 0 /\ (length name <= 15)%nat
  /\ (exists slack, bytes_at rsegs m (bv_unsigned r + Z.of_nat (length name) + 1) slack
        /\ Z.of_nat (length slack) = (- (bv_unsigned r + Z.of_nat (length name) + 1)) mod 8)
  /\ (bv_unsigned r + Z.of_nat (length name) + 8 <= lo \/ Sp <= bv_unsigned r)
  /\ (bv_unsigned r + Z.of_nat (length name) + 8 <= f \/ f + MemFile.MF_BLOCK <= bv_unsigned r).

Lemma name_ok_arg : forall m r name Sp lo f, name_ok m r name Sp lo f ->
  pf_arg_ok m Sp lo f MemFile.MF_BLOCK r (APtr (map bv_unsigned name)).
Proof.
  intros m r name Sp lo f (CS & NZ & _ & (slack & SB & SL) & F1 & F2).
  exact (name_arg_ok m r name slack Sp lo f MemFile.MF_BLOCK CS NZ SB SL F1 F2).
Qed.

Lemma read_emit : forall regs m f k name,
  arg regs 0 = f -> arg regs 3 = FMT_READ_A -> mem_inv rsegs m -> memfile_k m f k ->
  k + MARK_LINE_MAX <= MemFile.MF_BUFSIZ -> f <> 0 -> f + FILE_BLOCK <= spZ regs - 6112 ->
  name_ok m (getr regs 14) name (spZ regs) (spZ regs - 6112) f ->
  exists args T, emit_fmt m regs (arg regs 3) FMT_READ PS_READ args T
    /\ EMIT_HEAD + Z.of_nat (length T) <= MARK_LINE_MAX /\ ce_pre regs m.
Proof.
  intros regs m f k name A0 A3 MI MK FIT FN FB NO.
  destruct (text_read (map bv_unsigned name) (reac_served_mark_aux.sx32 (bv_unsigned (getr regs 15)))) as (T & TX).
  pose proof (len_read _ _ T (reac_served_mark_aux.sx32_range _) TX) as LT. rewrite length_map in LT.
  pose proof NO as (_ & _ & NL & _).
  assert (EF : emit_fmt m regs (arg regs 3) FMT_READ PS_READ
                 [APtr (map bv_unsigned name); AInt (reac_served_mark_aux.sx32 (bv_unsigned (getr regs 15)))] T).
  { destruct fmt_read_ok as (FBy & FR1 & FR2 & FP & _).
    unfold emit_fmt. rewrite A3.
    split; [exact (FBy m MI)|]. split; [exact FR1|]. split; [exact FR2|]. split; [exact FP|].
    split; [exact TX|].
    cbn [pf_args_ok]. split; [|split; [apply int_arg_ok | exact I]].
    rewrite A0. exact (name_ok_arg _ _ _ _ _ _ NO). }
  exists [APtr (map bv_unsigned name); AInt (reac_served_mark_aux.sx32 (bv_unsigned (getr regs 15)))], T.
  split; [exact EF|]. split; [unfold EMIT_HEAD, MARK_LINE_MAX; lia|].
  unfold ce_pre. cbv beta.
  exists FMT_READ, PS_READ, [APtr (map bv_unsigned name); AInt (reac_served_mark_aux.sx32 (bv_unsigned (getr regs 15)))], T, k.
  split; [rewrite A0; exact FN|]. split; [rewrite A3; unfold FMT_READ_A; lia|].
  split; [exact EF|]. split; [rewrite A0; exact MK|].
  split; [unfold EMIT_HEAD, MARK_LINE_MAX, MemFile.MF_BUFSIZ in *; lia|].
  rewrite A0. exact FB.
Qed.

Lemma mark_emit : forall regs m f k name capA cap capsl,
  arg regs 0 = f -> arg regs 3 = FMT_MARK_A -> getr regs 15 = Z_to_bv 64 S_SERVED_A ->
  getr regs 17 = Z_to_bv 64 capA -> str_ok capA cap capsl -> (cap = S_CAP \/ cap = S_EMPTY) ->
  mem_inv rsegs m -> memfile_k m f k ->
  k + MARK_LINE_MAX <= MemFile.MF_BUFSIZ -> f <> 0 -> f + FILE_BLOCK <= spZ regs - 6112 ->
  RO_END <= spZ regs - 6112 -> mf_place_ok f ->
  name_ok m (getr regs 14) name (spZ regs) (spZ regs - 6112) f ->
  exists args T, emit_fmt m regs (arg regs 3) FMT_MARK PS_MARK args T
    /\ EMIT_HEAD + Z.of_nat (length T) <= MARK_LINE_MAX /\ ce_pre regs m.
Proof.
  intros regs m f k name capA cap capsl A0 A3 G5 G7 SO CC MI MK FIT FN FB RO PL NO.
  destruct (text_mark (map bv_unsigned name) link_msgs_fit.S_SERVED (reac_served_mark_aux.sx32 (bv_unsigned (getr regs 16))) cap)
    as (T & TX).
  pose proof (len_mark _ _ _ T (reac_served_mark_aux.sx32_range _) TX) as LT. rewrite length_map in LT.
  assert (LC : Z.of_nat (length cap) <= 34) by (destruct CC as [-> | ->]; cbn; lia).
  pose proof NO as (_ & _ & NL & _).
  assert (PL' : f + MemFile.MF_BLOCK <= RO_LO \/ RO_END <= f)
    by (unfold mf_place_ok, IMG_LO, IMG_TOP, RO_LO, RO_END in *; lia).
  assert (EF : emit_fmt m regs (arg regs 3) FMT_MARK PS_MARK
                 [APtr (map bv_unsigned name); APtr link_msgs_fit.S_SERVED;
                  AInt (reac_served_mark_aux.sx32 (bv_unsigned (getr regs 16))); APtr cap] T).
  { destruct fmt_mark_ok as (FBy & FR1 & FR2 & FP & _).
    unfold emit_fmt. rewrite A3.
    split; [exact (FBy m MI)|]. split; [exact FR1|]. split; [exact FR2|]. split; [exact FP|].
    split; [exact TX|].
    cbn [pf_args_ok]. rewrite A0, G5, G7.
    split; [exact (name_ok_arg _ _ _ _ _ _ NO)|].
    split; [exact (ro_arg_ok m _ _ _ _ _ _ _ s_served_ok MI RO PL')|].
    split; [apply int_arg_ok|].
    split; [exact (ro_arg_ok m _ _ _ _ _ _ _ SO MI RO PL')|]. exact I. }
  exists [APtr (map bv_unsigned name); APtr link_msgs_fit.S_SERVED;
          AInt (reac_served_mark_aux.sx32 (bv_unsigned (getr regs 16))); APtr cap], T.
  split; [exact EF|]. split; [unfold EMIT_HEAD, MARK_LINE_MAX; lia|].
  unfold ce_pre. cbv beta.
  exists FMT_MARK, PS_MARK, [APtr (map bv_unsigned name); APtr link_msgs_fit.S_SERVED;
          AInt (reac_served_mark_aux.sx32 (bv_unsigned (getr regs 16))); APtr cap], T, k.
  split; [rewrite A0; exact FN|]. split; [rewrite A3; unfold FMT_MARK_A; lia|].
  split; [exact EF|]. split; [rewrite A0; exact MK|].
  split; [unfold EMIT_HEAD, MARK_LINE_MAX, MemFile.MF_BUFSIZ in *; lia|].
  rewrite A0. exact FB.
Qed.

(* fprintf's Pre, the text of lib/Prog/fprintf_c.v *)
Definition fp_pre (f k fl om wend wpos wbase pos len : Z) (pb : list byte)
    (fmt : list Z) (ps : list pf_piece) (args : list pf_arg) (T : list Z) :
    bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs m =>
       arg regs 0 = f /\
       memfile_k m f k /\ mf_dyn m f fl om wend wpos wbase pos len /\
       mf_pend_bytes m f pb /\ Z.of_nat (length pb) = k /\
       bytes_at rsegs m (arg regs 1) (pf_bytes (fmt ++ [0])) /\
       RO_LO <= arg regs 1 /\ arg regs 1 + Z.of_nat (length fmt) + 1 <= RO_END /\
       pf_parse fmt = Some ps /\ pf_text ps args = Some T /\
       pf_args_ok m (spZ regs) (spZ regs - FPRINTF_K) f MemFile.MF_BLOCK
         [getr regs 12; getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] args /\
       k + Z.of_nat (length T) <= MemFile.MF_BUFSIZ /\
       f + MemFile.MF_BLOCK <= spZ regs - FPRINTF_K /\ IMG_TOP <= spZ regs - FPRINTF_K /\
       guard_words m.

Lemma vlan_pre : forall regs m f k name,
  arg regs 0 = f -> arg regs 1 = FMT_VLAN_A -> mem_inv rsegs m -> memfile_k m f k ->
  k + MARK_LINE_MAX <= MemFile.MF_BUFSIZ ->
  f + MemFile.MF_BLOCK <= spZ regs - FPRINTF_K -> IMG_TOP <= spZ regs - FPRINTF_K -> guard_words m ->
  name_ok m (getr regs 12) name (spZ regs) (spZ regs - FPRINTF_K) f ->
  exists fl om wend wpos wbase pos len pb T, Z.of_nat (length T) <= MARK_LINE_MAX /\
    fp_pre f k fl om wend wpos wbase pos len pb FMT_VLAN PS_VLAN [APtr (map bv_unsigned name)] T regs m.
Proof.
  intros regs m f k name A0 A1 MI MK FIT FB IT GW NO.
  destruct (memfile_k_dyn m f k MK) as (fl & om & wend & wpos & wbase & pos & len & pb & MD & MP & LP).
  destruct (text_vlan (map bv_unsigned name)) as (T & TX).
  pose proof (len_vlan _ T TX) as LT. rewrite length_map in LT.
  pose proof NO as (_ & _ & NL & _).
  destruct fmt_vlan_ok as (FBy & FR1 & FR2 & FP & _).
  exists fl, om, wend, wpos, wbase, pos, len, pb, T.
  split; [unfold MARK_LINE_MAX; lia|].
  unfold fp_pre. rewrite A1.
  split; [exact A0|]. split; [exact MK|]. split; [exact MD|]. split; [exact MP|]. split; [exact LP|].
  split; [exact (FBy m MI)|]. split; [exact FR1|]. split; [exact FR2|]. split; [exact FP|].
  split; [exact TX|].
  split; [cbn [pf_args_ok]; split; [exact (name_ok_arg _ _ _ _ _ _ NO) | exact I]|].
  split; [unfold MARK_LINE_MAX, MemFile.MF_BUFSIZ in *; lia|].
  split; [exact FB|]. split; [exact IT|]. exact GW.
Qed.

Lemma host_pre : forall regs m f k name al big,
  arg regs 0 = f -> arg regs 1 = FMT_HOST_A -> mem_inv rsegs m -> memfile_k m f k ->
  k + MARK_LINE_MAX <= MemFile.MF_BUFSIZ ->
  f + MemFile.MF_BLOCK <= spZ regs - FPRINTF_K -> IMG_TOP <= spZ regs - FPRINTF_K -> guard_words m ->
  name_ok m (getr regs 12) name (spZ regs) (spZ regs - FPRINTF_K) f ->
  ~ In (zb 0) al -> Z.of_nat (length al) <= 255 ->
  bytes_at rsegs m (bv_unsigned (getr regs 13)) big -> firstn (S (length al)) big = al ++ [zb 0] ->
  (length al + 8 <= length big)%nat -> 0 < bv_unsigned (getr regs 13) ->
  spZ regs <= bv_unsigned (getr regs 13) -> f + MemFile.MF_BLOCK <= bv_unsigned (getr regs 13) ->
  exists fl om wend wpos wbase pos len pb T, Z.of_nat (length T) <= MARK_LINE_MAX /\
    fp_pre f k fl om wend wpos wbase pos len pb FMT_HOST PS_HOST
      [APtr (map bv_unsigned name); APtr (map bv_unsigned al)] T regs m.
Proof.
  intros regs m f k name al big A0 A1 MI MK FIT FB IT GW NO NN LA BB PR LB P0 S0 F0.
  destruct (memfile_k_dyn m f k MK) as (fl & om & wend & wpos & wbase & pos & len & pb & MD & MP & LP).
  destruct (text_host (map bv_unsigned name) (map bv_unsigned al)) as (T & TX).
  pose proof (len_host _ _ T TX) as LT. rewrite !length_map in LT.
  pose proof NO as (_ & _ & NL & _).
  destruct fmt_host_ok as (FBy & FR1 & FR2 & FP & _).
  exists fl, om, wend, wpos, wbase, pos, len, pb, T.
  split; [unfold MARK_LINE_MAX; lia|].
  unfold fp_pre. rewrite A1.
  split; [exact A0|]. split; [exact MK|]. split; [exact MD|]. split; [exact MP|]. split; [exact LP|].
  split; [exact (FBy m MI)|]. split; [exact FR1|]. split; [exact FR2|]. split; [exact FP|].
  split; [exact TX|].
  split.
  { cbn [pf_args_ok]. split; [exact (name_ok_arg _ _ _ _ _ _ NO)|].
    split; [|exact I].
    apply (alias_arg_ok m _ al big); try assumption; [right; exact S0 | right; exact F0]. }
  split; [unfold MARK_LINE_MAX, MemFile.MF_BUFSIZ in *; lia|].
  split; [exact FB|]. split; [exact IT|]. exact GW.
Qed.

(* the alias a read leaves fits its buffer *)
Lemma read_alias_len : forall tab nm kc ac reqs K, 1 <= ac ->
  Z.of_nat (length (r_alias (read_core tab nm kc ac reqs K))) <= ac - 1.
Proof.
  intros tab nm kc ac reqs K H. unfold read_core. destruct nm as [s|]; [|cbn; lia].
  destruct (Nat.eqb (length s) 0); [cbn; lia|].
  destruct (index_of tab s =? 0); [cbn; lia|].
  cbn [r_alias]. destruct (ac <? 1); [cbn; lia|]. apply text_of_attr_len. lia.
Qed.

Lemma cb_bytes : forall m A n j, rw_cells rsegs m A [CB n j] -> bytes_at rsegs m A j /\ length j = n.
Proof. intros m A n j [[Hwf Hb] _]. cbn in Hwf, Hb. rewrite app_nil_r in Hb. split; [exact Hb | exact (proj1 Hwf)]. Qed.

(* "%s", remember's format, out of the image *)
Lemma fmt_s_at : forall m, mem_inv rsegs m -> cstr_at m A_FMT_S (map (Z_to_bv 8) [37; 115]).
Proof.
  intros m MI. split.
  - apply ro_bytes_at; [exact MI | unfold A_FMT_S; lia | cbn; unfold A_FMT_S; lia |].
    unfold A_FMT_S. vm_compute. repeat split; reflexivity.
  - apply no_nul_check. vm_compute. reflexivity.
Qed.

Definition rm_pre := ltac:(let t := eval cbv delta [remember_contract] in remember_contract in
  match t with leaf_fp _ _ ?P _ _ => exact P end).

(* remember's Pre at 0x165c8 and 0x1660c: m = the marks block, ifname = the name *)
Lemma remember_pre : forall regs m gbs name slack,
  marks_at m (arg regs 0) gbs -> marks_wf gbs -> arg regs 1 <> 0 -> cstr_at m (arg regs 1) name ->
  (length name <= 15)%nat -> mem_inv rsegs m ->
  apart (arg regs 1) (Z.of_nat (length name) + 8) (arg regs 0) MK_SIZE ->
  pf_img_free (arg regs 0) MK_SIZE ->
  bytes_at rsegs m (arg regs 1 + Z.of_nat (length name) + 1) slack ->
  Z.of_nat (length slack) = (- (arg regs 1 + Z.of_nat (length name) + 1)) mod 8 ->
  apart_frame regs 6400 (arg regs 0) MK_SIZE -> apart_frame regs 6400 (arg regs 1) (Z.of_nat (length name) + 8) ->
  rm_pre regs m.
Proof.
  intros regs m gbs name slack G GW A1 C L MI AP PF SB SL F0 F1.
  unfold rm_pre. cbv beta. exists gbs, name.
  split; [exact G|]. split; [exact GW|]. split; [exact A1|]. split; [exact C|]. split; [exact L|].
  split; [exact (fmt_s_at m MI)|]. split; [unfold apart in AP; lia|]. split; [exact PF|].
  split; [exists slack; split; assumption|]. split; assumption.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [B1 B2].
  rewrite cells_size_app in Hw. destruct Hw as (Ha & Hn & Hw).
  rewrite (cells_bytes_length cs1 W1) in B2.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

(* the 320-byte frame after the four saves: alias[256] at +0, kind[32] at +256, the saves at +288 *)
Lemma frame_split : forall m A (j : list byte) x1 x2 x3 x4,
  rw_cells rsegs m A [CB 288 j; C8 x1; C8 x2; C8 x3; C8 x4] ->
  (exists jb, rw_cells rsegs m A [CB 256 jb]) /\ (exists jk, rw_cells rsegs m (A + 256) [CB 32 jk])
  /\ rw_cells rsegs m (A + 288) [C8 x1; C8 x2; C8 x3; C8 x4].
Proof.
  intros m A j x1 x2 x3 x4 H.
  apply (rw_cells_split_CB rsegs m A [] 288 j _ [256%nat; 32%nat]) in H; [|reflexivity].
  cbn [app mk_CB_cells] in H.
  apply (rw_cells_app m A [CB 256 (firstn 256 j)]) in H as [H1 H].
  apply (rw_cells_app m _ [CB 32 _]) in H as [H2 H3].
  cbn [cells_size csize Nat.add] in *.
  split; [eexists; exact H1|]. split.
  - eexists. replace (A + 256) with (A + Z.of_nat 256) by reflexivity. exact H2.
  - replace (A + 288) with (A + Z.of_nat 256 + Z.of_nat 32) by (cbn; lia). exact H3.
Qed.

(* The separation facts stay folded (apart, apart_gnl, apart_frame, frame_apart_gnl, mf_place_ok)
   so that the many `lia` calls of the walk tactics see no disjunction; `dj H..` clears all but
   the named facts, unfolds them and decides the goal. *)
Ltac cst := unfold frame_apart_gnl, apart_frame, mf_place_ok, mf_block, apart, apart_gnl in *;
  rewrite ?mkR_sp in *;
  unfold A_G_NL, NK_SIZE, NK_N_SENT, NK_IF_NAME, MK_SIZE, FILE_BLOCK,
  MemFile.MF_BLOCK, IMG_LO, IMG_TOP, A_IMG_TOP, A_G_SAY, A_GOT_GUARD, A_GUARD, A_G_SAID, SAID_SIZE,
  ERRNO_TP_OFF, MARK_LINE_MAX, MemFile.MF_BUFSIZ in *.
Tactic Notation "dj" ne_hyp_list(l) :=
  clear - l; cst; cbn [disjoint_from outside] in *; repeat split; try exact I; lia.
Tactic Notation "dj0" := clear; cst; cbn [disjoint_from outside]; repeat split; try exact I; lia.

(* bv_unsigned of a literal-built word *)
Ltac ulit := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.

(* a branch whose condition is a closed term *)
Ltac lit_branch :=
  match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let v := eval vm_compute in c in change c with v; cbv iota end.

(* the epilogue at 0x164f0: mv a0, s1; the four reloads; addi sp; ret *)
Ltac exit7 := zstep; zstep; zstep; zstep; zstep; zstep; zstep.

(* the first four parts of the leaf_fp result: the state, frm0, the FP file, regs_preserved *)
Ltac fin_start :=
  apply evt_done; do 4 eexists; split; [reflexivity|];
  split; [assumption|]; split; [first [intros; reflexivity | assumption]|];
  split; [eapply regs_preserved_mkR|].

Theorem reac_served_mark_walk :
  reac_link_alias_read_contract -> reac_served_decide_contract -> reac_link_alias_write_contract ->
  remember_contract -> reac_code_emit_contract -> fprintf_contract -> bcmp_contract ->
  forall sink, leaf_fp_walk REAC_SERVED_MARK 17248 (mk_pre sink) (mk_wr sink) (mk_post sink).
Proof.
  intros HAR HDE HAW HRM HCE HFP HBC sink.
  unfold leaf_fp_walk, REAC_SERVED_MARK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  cbv zeta. intros PRE MI TM ST LO SP FRM ITOP GG GQ.
  pose proof (conj GG GQ) as GW. clear GG GQ.
  unfold mk_pre, mk_wr, mk_post in *.
  destruct PRE as (kbs & tab & nm & k & NLK & FAG & WF & OPEN & OPN & CLS & TAB & ERR & TOK & POL & SAY
                   & SNZ & MF & MFK & SNB & NMA & NOK & BOK).
  unfold mark_errno_ok, mark_table_ok, mark_name_ok, mark_block_ok in *.
  rewrite ?mkR_sp, ?mkR_a0, ?mkR_a1, ?mkR_errno in *.
  destruct ERR as (EW & EF & EG & ES & EGG & ESAY & ESAID & ELO & EHI).
  pose proof (memfile_k_place _ _ _ MF) as MFP.
  assert (SPT : bv_unsigned sp <= TASK_SIZE)
    by (apply (sp_task m lo (bv_unsigned sp) TM ST); [unfold A_IMG_TOP, IMG_TOP in *; lia | lia]).
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (TASKW : forall x, 0 <= x < 2 ^ 64 ->
     ~ outside [(bv_unsigned sp - 17248, bv_unsigned sp); (A_G_NL, A_G_NL + NK_N_SENT + 4);
                (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4)] x -> x < TASK_SIZE).
  { intros x _ H. destruct (Z_lt_le_dec x TASK_SIZE) as [?|Hx]; [assumption|]. exfalso. apply H.
    assert (T47 : TASK_SIZE = 2 ^ 47) by reflexivity.
    dj SPT EHI Hx T47. }
  pose proof (munch_refl [(bv_unsigned sp - 17248, bv_unsigned sp)] m) as MU0.
  pose proof (munch_refl [(bv_unsigned sp - 17248, bv_unsigned sp); (A_G_NL, A_G_NL + NK_N_SENT + 4);
     (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4)] m) as MUf.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 320%nat ST.
  zstep. zstep. zstep. zstep. zstep.
  destruct (frame_split _ _ _ _ _ _ _ FR) as ((jb & FRB) & (jk & FRK) & FRS). clear FR.
  replace (bv_unsigned sp + -320 + 256) with (bv_unsigned sp + -64) in FRK by lia.
  replace (bv_unsigned sp + -320 + 288) with (bv_unsigned sp + -32) in FRS by lia.
  match goal with |- evt _ ?Q _ => assert (HQ : q_ext Q)
    by (apply leaf_fp_q_ext; intros q1 q2 mq E H; rewrite <- !E; exact H) end.
  (* the FILE, untouched by the frame stores and the leaf callees' g_nl / errno writes *)
  assert (MFD : disjoint_from [(bv_unsigned sp - 17248, bv_unsigned sp); (A_G_NL, A_G_NL + NK_N_SENT + 4);
     (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4)] sink MemFile.MF_BLOCK)
    by dj SNB MFP ES.
  assert (NLD : disjoint_from [(bv_unsigned sp - 17248, bv_unsigned sp)] A_G_NL NK_SIZE) by dj FAG.
  zstep. zstep.
  destruct (Z.eq_dec (bv_unsigned a0) 0) as [A0Z|A0N].
  { (* 0x16488: a NULL marks block *)
    if_true. exit7.
    release_frame FRB ST (bv_unsigned sp + -64). release_frame FRK ST (bv_unsigned sp + -32).
    release_frame FRS ST (bv_unsigned sp).
    fin_start.
    split. { eapply munch_weaken; [|exact MUf]. intros x Hx. unfold mf_block in Hx. cbn [outside] in *. tauto. }
    split; [exact WM|]. split; [exact MI|]. split; [exact (task_mem_munch _ _ _ TM MUf TASKW)|].
    split; [exact ST|].
    split. { intros k0 Hk. exists k0. split; [unfold MARK_LINE_MAX; lia|]. exact (memfile_k_transport _ _ _ _ _ Hk MUf WM MFD). }
    split. { intros _. split; [reflexivity|]. intros kbs0 Hn. exact (nlk_transport _ _ _ _ Hn MU0 WM NLD). }
    intros Hc. exfalso. exact (Hc A0Z). }
  assert (A0E : (bv_unsigned a0 =? 0) = false) by (apply Z.eqb_neq; exact A0N).
  rewrite A0E in HQ |- *.
  destruct (BOK A0N) as (MKF & MKG & MKE & MKS & MKI & gbs & GBS & GWF). clear BOK.
  assert (MKD : disjoint_from [(bv_unsigned sp - 17248, bv_unsigned sp); (A_G_NL, A_G_NL + NK_N_SENT + 4);
     (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4)] (bv_unsigned a0) MK_SIZE)
    by dj MKF MKG MKE.
  assert (SLD : disjoint_from [(bv_unsigned sp - 17248, bv_unsigned sp)]
                  (A_G_NL + NK_IF_NAME) (NK_SIZE - NK_IF_NAME)) by dj FAG.
  (* the refusal answer, once the name is NULL or empty *)
  assert (REF : forall mq, munch [(bv_unsigned sp - 17248, bv_unsigned sp)] m mq -> wmono rsegs m mq ->
     (forall nm0, str_arg m (bv_unsigned a1) nm0 -> nm0 = None \/ nm0 = Some []) ->
     post_marks (bv_unsigned a0) (bv_unsigned a1) m (wz (- E_INVAL)) mq).
  { intros mq M1 W1 HS.
    refine (marks_refused m mq (bv_unsigned a0) (bv_unsigned a1) kbs tab NLK WF OPEN TAB
              (ex_intro _ gbs (conj GBS GWF)) _ _ _ HS).
    - intros kbs0 Hn. exact (nlk_transport _ _ _ _ Hn M1 W1 NLD).
    - intros tab0 T0. rewrite (iftab_unique _ _ _ _ T0 TAB).
      apply (iftab_transport _ _ _ _ _ TAB M1 SLD).
      intros i n2 ix p Hi Hp. destruct (TOK i n2 ix p Hi Hp) as (Fp & _). dj Fp.
    - intros g G. apply (marks_transport _ _ _ _ _ G M1 W1). dj MKF. }
  assert (B0 : bv_eqb a0 (Z_to_bv 64 0) = false) by exact A0E.
  rewrite B0. cbv iota. zstep. zstep.
  destruct nm as [s|].
  2:{ (* 0x16490: a NULL name *)
    cbn in NMA. if_true. exit7.
    release_frame FRB ST (bv_unsigned sp + -64). release_frame FRK ST (bv_unsigned sp + -32).
    release_frame FRS ST (bv_unsigned sp).
    fin_start.
    split. { eapply munch_weaken; [|exact MUf]. intros x Hx. unfold mf_block in Hx. cbn [outside] in *. tauto. }
    split; [exact WM|]. split; [exact MI|]. split; [exact (task_mem_munch _ _ _ TM MUf TASKW)|].
    split; [exact ST|].
    split. { intros k0 Hk. exists k0. split; [unfold MARK_LINE_MAX; lia|]. exact (memfile_k_transport _ _ _ _ _ Hk MUf WM MFD). }
    split. { intros Hc. exfalso. exact (A0N Hc). }
    intros _. apply (REF _ MU0 WM). intros [s0'|] H0; [|left; reflexivity]. exfalso. exact (proj1 H0 NMA). }
  destruct NMA as [A1N CS].
  destruct (NOK s eq_refl) as (SL & SF & SG & SS & SE & (slack & SLB & SLL) & SM). clear NOK.
  specialize (SM A0N).
  assert (CS1 : bytes_at rsegs m1 (bv_unsigned a1) (s ++ [zb 0])).
  { eapply bytes_at_transport; [exact (proj1 CS) | exact MU0 |].
    rewrite length_app. cbn [length]. dj SF. }
  if_false. zstep.
  destruct s as [|x s'].
  { (* 0x1649c: an empty name *)
    pose proof (bytes_at_read1 m1 a1 (zb 0) [] CS1) as HR.
    zstep. unfold zb. zstep. if_true. exit7.
    release_frame FRB ST (bv_unsigned sp + -64). release_frame FRK ST (bv_unsigned sp + -32).
    release_frame FRS ST (bv_unsigned sp).
    fin_start.
    split. { eapply munch_weaken; [|exact MUf]. intros y Hy. unfold mf_block in Hy. cbn [outside] in *. tauto. }
    split; [exact WM|]. split; [exact MI|]. split; [exact (task_mem_munch _ _ _ TM MUf TASKW)|].
    split; [exact ST|].
    split. { intros k0 Hk. exists k0. split; [unfold MARK_LINE_MAX; lia|]. exact (memfile_k_transport _ _ _ _ _ Hk MUf WM MFD). }
    split. { intros Hc. exfalso. exact (A0N Hc). }
    intros _. apply (REF _ MU0 WM). intros nm0 H0. right.
    exact (str_arg_unique m (bv_unsigned a1) nm0 (Some []) H0 (conj A1N CS)). }
  assert (Hx : bv_unsigned x <> 0).
  { intros E. apply (proj2 CS). left. apply byte_zero. exact E. }
  pose proof (bytes_at_read1 m1 a1 x (s' ++ [zb 0]) CS1) as HR.
  zstep. zstep.
  assert (Ex : bv_eqb (Z_to_bv 64 (bv_unsigned x)) (Z_to_bv 64 0) = false).
  { rewrite bv_eqb_lit by (pose proof (byte_range x); lia). apply Z.eqb_neq. exact Hx. }
  rewrite Ex. cbv iota.
  zstep. zstep. zstep. zstep. zstep. zstep.
  (* 0x164b4: reac_link_alias_read(ifname, kind = sp+0x100, 32, alias = sp, 256) *)
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -320)) = bv_unsigned sp + -320)
    by (apply unsigned_lit; lia).
  assert (CSm1 : cstr_at m1 (bv_unsigned a1) (x :: s')) by (split; [exact CS1 | exact (proj2 CS)]).
  assert (TAB1 : iftab_at m1 kbs tab).
  { apply (iftab_transport _ _ _ _ _ TAB MU0 SLD).
    intros i n2 ix p Hi Hp. destruct (TOK i n2 ix p Hi Hp) as (Fp & _). dj Fp. }
  pose proof (nlk_transport _ _ _ _ NLK MU0 WM NLD) as NLK1.
  eapply (leaf_call _ _ _ _ _ HAR).
  { post_ext_tac. }
  { exact HQ. }
  { cbv beta. exists kbs, tab, (Some (x :: s')).
    rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_errno.
    ulit.
    split; [exact NLK1|].
    split; [dj FAG ESP|].
    split; [exact WF|]. split; [exact OPEN|]. split; [lia|]. split; [lia|].
    split; [exact TAB1|].
    split; [exact EW|].
    split; [dj EF ESP|].
    split; [exact EG|].
    split; [split; [exact A1N | exact CSm1]|].
    split; [intros _ _; exists jk; exact FRK|].
    split; [intros _ _; exists jb; exact FRB|].
    split.
    { intros i n2 ix p Hi Hp.
      assert (Hi80 : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      pose proof TAB as (_ & TL & _).
      assert (Hp0 : u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
      { apply (u64_back _ _ _ _ _ Hp MU0). dj FAG TL Hi80. }
      destruct (TOK i n2 ix p Hi Hp0) as (T1 & T2 & T3 & _).
      split; [dj T1 ESP|]. split; [exact T2|]. split; [exact T3|].
      split; intros; dj T1. }
    split. { intros sq Hs. injection Hs as Hs. subst sq. split; intros; dj SF. }
    split; [intros; unfold apart; lia|].
    split; [intros; dj EF|].
    split; [intros; dj EF|].
    split. { intros sq Hs. injection Hs as Hs. subst sq. split; [dj SF ESP | dj SG]. }
    split; [intros; split; [dj ESP | dj FAG]|].
    intros; split; [dj ESP | dj FAG]. }
  { exact MI. }
  { rewrite ESP. exact ST. }
  { rewrite ESP. lia. }
  { rewrite ESP. lia. }
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 PO.
  cbv beta in PO, MU2.
  specialize (PO kbs tab (Some (x :: s')) NLK1 TAB1 (conj A1N CSm1)).
  rewrite ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_errno in PO, MU2.
  rewrite (unsigned_lit 32), (unsigned_lit 256), (unsigned_lit (bv_unsigned sp + -64)), ESP in PO, MU2 by lia.
  replace (bv_unsigned sp + -64 =? 0) with false in MU2 by (symmetry; apply Z.eqb_neq; lia).
  replace (bv_unsigned sp + -320 =? 0) with false in MU2 by (symmetry; apply Z.eqb_neq; lia).
  destruct PO as (RC & (kbs1 & NLK2 & WF2 & CH2 & EE2 & NIF2 & TAB2 & NX2 & SK2 & SD2 & SENT2 & NSENT2
                  & OPEN2 & MIS2 & OC2 & OB2 & OZ2) & KIND2 & ALIAS2 & KBUF2 & ABUF2).
  rewrite ret_pc_even by (lia || reflexivity).
  set (R := read_lib tab (Some (x :: s')) 32 256 (nk_sent kbs) (nk_kstate kbs)) in *.
  assert (EA0 : a0' = wz (r_rc R)) by exact RC. subst a0'.
  assert (RCR : - 2 ^ 31 <= r_rc R < 2 ^ 31).
  { destruct (kstate_bounds kbs WF) as (B1 & B2 & B3). exact (read_rc_range _ _ _ _ _ _ B1 B2 B3). }
  rewrite mkR_errno in MU2. rewrite ESP in ST2.
  specialize (KIND2 ltac:(lia) ltac:(lia)). specialize (ALIAS2 ltac:(lia) ltac:(lia)).
  destruct (KBUF2 ltac:(lia) ltac:(lia)) as (jk2 & FRK2). destruct (ABUF2 ltac:(lia) ltac:(lia)) as (jb2 & FRB2).
  clear KBUF2 ABUF2 RC.
  assert (FRS2 : rw_cells rsegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FRS MU2 WM2). cbn [cells_size csize Nat.add]. dj FAG EF. }
  assert (MUf2 : munch [(bv_unsigned sp - 17248, bv_unsigned sp); (A_G_NL, A_G_NL + NK_N_SENT + 4);
     (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4)] m m2).
  { apply (munch_trans _ m m1 m2 MUf). eapply munch_weaken; [|exact MU2].
    intros y Hy. cbn [outside] in *. destruct Hy as (H1 & H2 & H3 & _).
    repeat split; try exact I; try assumption; lia. }
  pose proof (wmono_trans rsegs m m1 m2 WM WM2) as WMf2.
  assert (TM2 : task_mem rsegs m2) by exact (task_mem_munch _ _ _ TM MUf2 TASKW).
  assert (MF2 : memfile_k m2 sink k) by exact (memfile_k_transport _ _ _ _ _ MF MUf2 WMf2 MFD).
  assert (GG2 : bytes_at rsegs m2 A_GOT_GUARD (le8 (wz A_GUARD))).
  { apply (bytes_at_transport rsegs _ _ _ _ _ (proj1 GW) MUf2). rewrite length_le8. dj EGG ITOP LO. }
  assert (NM2 : cstr_at m2 (bv_unsigned a1) (x :: s')).
  { apply (cstr_transport _ _ _ _ _ CS MUf2). dj SF SG SE. }
  assert (SL2 : bytes_at rsegs m2 (bv_unsigned a1 + Z.of_nat (length (x :: s')) + 1) slack).
  { apply (bytes_at_transport rsegs _ _ _ _ _ SLB MUf2). dj SF SG SE SLL. }
  assert (SAY2 : bytes_at rsegs m2 480560 (le8 (Z_to_bv 64 sink))).
  { apply (bytes_at_transport rsegs _ _ _ _ _ SAY MUf2). rewrite length_le8. dj ESAY ITOP LO. }
  assert (HRS : ov_read_bytes rsegs m2 (Z_to_bv 64 480560) 8 = Some (le8 (Z_to_bv 64 sink))).
  { pose proof (bytes_at_read rsegs m2 480560 (le8 (Z_to_bv 64 sink)) 0 8 SAY2 ltac:(lia)
                  ltac:(rewrite length_le8; cbn; lia)) as H.
    rewrite Z.add_0_r in H. unfold wa in H. rewrite H.
    try (f_equal; cbn [Z.to_nat skipn]; apply firstn_all2; rewrite length_le8; lia). }
  pose proof (memfile_k_at _ _ _ MF) as (SK0 & SK64 & _). unfold MemFile.MF_BLOCK in SK64.
  assert (SKE : bv_eqb (Z_to_bv 64 sink) (Z_to_bv 64 0) = false)
    by (rewrite bv_eqb_lit by (unfold FILE_BLOCK, MemFile.MF_BLOCK in *; lia); apply Z.eqb_neq; lia).
  zstep.
  unfold wz. rewrite bv_eqb_z0 by lia.
  destruct (Z.eqb_spec (r_rc R) 0) as [RC0|RCN]; cbv iota.
  2:{ (* 0x164bc: the read failed; say() is g_say; reac_code_emit(f, 0, fmt, ifname, -rc) at 0x164ec *)
    zstep. zstep. zstep. zstep.
    rewrite SKE. cbn [negb]. cbv iota.
    zstep. zstep. zstep. zstep. zstep. zstep.
    match goal with |- evt _ _ (MS ?Rg _ _ _ _ _ _) =>
      assert (A0R : arg Rg 0 = sink)
        by (unfold arg; change (bv_unsigned (Z_to_bv 64 sink) = sink); apply unsigned_lit; lia);
      assert (A3R : arg Rg 3 = FMT_READ_A) by (unfold arg; reflexivity);
      assert (SPR : spZ Rg = bv_unsigned sp + -320)
        by (unfold spZ; change (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -320)) = bv_unsigned sp + -320);
            exact ESP);
      assert (NO : name_ok m2 (getr Rg 14) (x :: s') (spZ Rg) (spZ Rg - 6112) sink)
        by (change (getr Rg 14) with a1; rewrite SPR; unfold name_ok;
            split; [exact NM2|]; split; [exact A1N|]; split; [exact SL|];
            split; [exists slack; split; [exact SL2 | exact SLL]|]; split; [dj SF ESP | dj SS]);
      destruct (read_emit Rg m2 sink k (x :: s') A0R A3R MI2 MF2 MFK SNZ
                  ltac:(rewrite SPR; unfold FILE_BLOCK in *; lia) NO) as (eargs & T & EFM & LT & CPRE)
    end.
    eapply (leaf_fp_call _ _ _ _ _ HCE).
    { post_ext_tac. }
    { exact HQ. }
    { exact CPRE. }
    { exact MI2. }
    { exact TM2. }
    { rewrite ESP. exact ST2. }
    { rewrite ESP. lia. }
    { rewrite ESP. lia. }
    { exact FRM. }
    { exact ITOP. }
    { exact GG2. }
    { exact (guard_any m2). }
    intros ra3 t03 t13 t23 a03 a13 a23 a33 a43 a53 a63 a73 t33 t43 t53 t63 Ft3 fc3 m3
      FRM3 FK3 MU3 WM3 MI3 TM3 ST3 PO3.
    cbv beta in PO3, MU3.
    rewrite ?mkR_a0 in PO3, MU3. rewrite (unsigned_lit sink) in PO3, MU3 by lia.
    rewrite ESP in MU3, ST3.
    pose proof (PO3 _ _ _ _ _ EFM MF2) as MF3. clear PO3.
    rewrite ret_pc_even by (lia || reflexivity).
    unfold mf_block in MU3. cbn [fst snd] in MU3.
    assert (FRS3 : rw_cells rsegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply (rw_cells_transport rsegs _ m2 m3 _ _ FRS2 MU3 WM3); cbn [cells_size csize Nat.add]; dj SNB).
    assert (FRK3 : rw_cells rsegs m3 (bv_unsigned sp + -64) [CB (Z.to_nat 32) jk2])
      by (apply (rw_cells_transport rsegs _ m2 m3 _ _ FRK2 MU3 WM3); cbn [cells_size csize Nat.add]; dj SNB).
    assert (FRB3 : rw_cells rsegs m3 (bv_unsigned sp + -320) [CB (Z.to_nat 256) jb2])
      by (apply (rw_cells_transport rsegs _ m2 m3 _ _ FRB2 MU3 WM3); cbn [cells_size csize Nat.add]; dj SNB).
    exit7.
    release_frame FRB3 ST3 (bv_unsigned sp + -64). release_frame FRK3 ST3 (bv_unsigned sp + -32).
    release_frame FRS3 ST3 (bv_unsigned sp).
    fin_start.
    split.
    { apply (munch_trans _ m m2 m3).
      - eapply munch_weaken; [|exact MUf2]. intros y Hy. unfold mf_block in Hy. cbn [outside] in *. tauto.
      - eapply munch_weaken; [|exact MU3]. intros y Hy. unfold mf_block in Hy. cbn [outside fst snd] in *.
        destruct Hy as (H1 & H2 & H3 & H4 & H5 & _). repeat split; try exact I; try assumption; lia. }
    split; [exact (wmono_trans rsegs m m2 m3 WMf2 WM3)|]. split; [exact MI3|]. split; [exact TM3|].
    split; [exact ST3|].
    split.
    { intros k0 Hk. rewrite (memfile_k_unique _ _ _ _ Hk MF). exists (k + EMIT_HEAD + Z.of_nat (length T)).
      split; [unfold EMIT_HEAD, MARK_LINE_MAX in *; lia | exact MF3]. }
    split. { intros Hc. exfalso. exact (A0N Hc). }
    intros _.
    refine (post_marks_of m m3 _ _ kbs tab (Some (x :: s')) gbs _
              (Mres (r_rc R) (mk_names gbs) (r_reqs R) (r_state R)) kbs1 gbs NLK TAB (conj A1N CS) GBS
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + rewrite mark_lib_some. cbv zeta.
      change (read_core tab (Some (x :: s')) 32 256 (nk_sent kbs) (nk_kstate kbs)) with R.
      replace (r_rc R =? 0) with false by (symmetry; apply Z.eqb_neq; exact RCN). reflexivity.
    + reflexivity.
    + apply (marks_transport _ _ _ _ _ (marks_transport _ _ _ _ _ GBS MUf2 WMf2 MKD) MU3 WM3). dj MKF MKS.
    + exact GWF.
    + reflexivity.
    + apply (nlk_transport _ _ _ _ NLK2 MU3 WM3). dj FAG MFP.
    + exact WF2.
    + exact CH2.
    + exact EE2.
    + exact NIF2.
    + apply (iftab_transport _ _ _ _ _ TAB2 MU3); [dj FAG MFP|].
      intros i n2 ix p Hi Hp.
      assert (Hi80 : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      pose proof TAB as (_ & TL & _).
      assert (Hp0 : u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
      { apply (u64_back _ _ _ _ _ Hp MUf2). dj FAG TL Hi80 EG. }
      destruct (TOK i n2 ix p Hi Hp0) as (T1 & _ & _ & T4 & _). dj T1 T4.
    + exact NX2.
    + exact SENT2.
    + exact NSENT2.
    + exact OPEN2.
    + exact MIS2.
    + exact OC2.
    + lia. }
  (* 0x1650c: reac_served_decide(kind = sp+0x100, alias = sp) *)
  zstep. zstep. zstep.
  eapply (leaf_call _ _ _ _ _ HDE).
  { post_ext_tac. }
  { exact HQ. }
  { cbv beta. exists (Some (r_kind R)), (Some (r_alias R)).
    rewrite ?mkR_a0, ?mkR_a1. ulit.
    split; [split; [lia | exact KIND2]|].
    split; [split; [lia | exact ALIAS2]|].
    split; [intros t Ht; dj ESP|].
    split; [intros t Ht; dj ESP|].
    split; [split; [exact (prefix_at m2 MI2) | exact S_PREFIX_no_nul]|].
    split; [exact (vlan_at m2 MI2) | exact S_VLAN_no_nul]. }
  { exact MI2. }
  { rewrite ESP. exact ST2. }
  { rewrite ESP. lia. }
  { rewrite ESP. lia. }
  intros ra4 t04 t14 t24 a04 a14 a24 a34 a44 a54 a64 a74 t34 t44 t54 t64 m3 MU3 WM3 MI3 ST3 PO3.
  cbv beta in PO3, MU3. cbn [writes_nothing] in MU3. rewrite ESP in MU3, ST3.
  rewrite ?mkR_a0, ?mkR_a1 in PO3.
  rewrite (unsigned_lit (bv_unsigned sp + -64)), (unsigned_lit (bv_unsigned sp + -320)) in PO3 by lia.
  assert (SPK : bv_unsigned sp + -64 <> 0) by lia. assert (SPA : bv_unsigned sp + -320 <> 0) by lia.
  specialize (PO3 (Some (r_kind R)) (Some (r_alias R)) (conj SPK KIND2) (conj SPA ALIAS2)).
  set (V := decide (Some (r_kind R)) (Some (r_alias R))) in *.
  assert (EA4 : a04 = wz V) by exact PO3. subst a04. clear PO3.
  rewrite ret_pc_even by (lia || reflexivity).
  (* the facts of m2 the four verdicts use, kept by the decider's 16-byte frame *)
  assert (D3 : forall a n, (bv_unsigned sp + -320 <= a \/ a + n <= bv_unsigned sp + -320 - 16) ->
                 disjoint_from [(bv_unsigned sp + -320 - 16, bv_unsigned sp + -320)] a n)
    by (intros a n H; cbn [disjoint_from]; split; [lia | exact I]).
  assert (FRS3 : rw_cells rsegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
    by (apply (rw_cells_transport rsegs _ m2 m3 _ _ FRS2 MU3 WM3); apply D3; left; lia).
  assert (FRK3 : rw_cells rsegs m3 (bv_unsigned sp + -64) [CB (Z.to_nat 32) jk2])
    by (apply (rw_cells_transport rsegs _ m2 m3 _ _ FRK2 MU3 WM3); apply D3; left; lia).
  assert (FRB3 : rw_cells rsegs m3 (bv_unsigned sp + -320) [CB (Z.to_nat 256) jb2])
    by (apply (rw_cells_transport rsegs _ m2 m3 _ _ FRB2 MU3 WM3); apply D3; left; lia).
  assert (ALIAS3 : cstr_at m3 (bv_unsigned sp + -320) (r_alias R))
    by (apply (cstr_transport _ _ _ _ _ ALIAS2 MU3); apply D3; left; lia).
  assert (NLK3 : nlk_at m3 kbs1) by (apply (nlk_transport _ _ _ _ NLK2 MU3 WM3); dj FAG).
  assert (MUf3 : munch [(bv_unsigned sp - 17248, bv_unsigned sp); (A_G_NL, A_G_NL + NK_N_SENT + 4);
     (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4)] m m3).
  { apply (munch_trans _ m m2 m3 MUf2). eapply munch_weaken; [|exact MU3].
    intros y Hy. cbn [outside] in *. destruct Hy as (H1 & _). split; [lia | exact I]. }
  pose proof (wmono_trans rsegs m m2 m3 WMf2 WM3) as WMf3.
  assert (TAB3 : iftab_at m3 kbs1 tab).
  { apply (iftab_transport _ _ _ _ _ TAB2 MU3); [dj FAG|].
    intros i n2 ix p Hi Hp.
    assert (Hi80 : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    pose proof TAB as (_ & TL & _).
    assert (Hp0 : u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
    { apply (u64_back _ _ _ _ _ Hp MUf2). dj FAG TL Hi80 EG. }
    destruct (TOK i n2 ix p Hi Hp0) as (T1 & _). dj T1. }
  clear FRS2 FRK2 FRB2 NLK2 TAB2.
  assert (TM3 : task_mem rsegs m3) by exact (task_mem_munch _ _ _ TM MUf3 TASKW).
  assert (MF3 : memfile_k m3 sink k) by exact (memfile_k_transport _ _ _ _ _ MF MUf3 WMf3 MFD).
  assert (GG3 : bytes_at rsegs m3 A_GOT_GUARD (le8 (wz A_GUARD))).
  { apply (bytes_at_transport rsegs _ _ _ _ _ (proj1 GW) MUf3). rewrite length_le8. dj EGG ITOP LO. }
  assert (GW3 : guard_words m3) by exact (conj GG3 (guard_any m3)).
  assert (NM3 : cstr_at m3 (bv_unsigned a1) (x :: s')).
  { apply (cstr_transport _ _ _ _ _ CS MUf3). dj SF SG SE. }
  assert (SL3 : bytes_at rsegs m3 (bv_unsigned a1 + Z.of_nat (length (x :: s')) + 1) slack).
  { apply (bytes_at_transport rsegs _ _ _ _ _ SLB MUf3). dj SF SG SE SLL. }
  assert (HRS3 : ov_read_bytes rsegs m3 (Z_to_bv 64 480560) 8 = Some (le8 (Z_to_bv 64 sink))).
  { assert (SAY3 : bytes_at rsegs m3 480560 (le8 (Z_to_bv 64 sink))).
    { apply (bytes_at_transport rsegs _ _ _ _ _ SAY MUf3). rewrite length_le8. dj ESAY ITOP LO. }
    pose proof (bytes_at_read rsegs m3 480560 (le8 (Z_to_bv 64 sink)) 0 8 SAY3 ltac:(lia)
                  ltac:(rewrite length_le8; cbn; lia)) as H.
    rewrite Z.add_0_r in H. unfold wa in H. rewrite H.
    try (f_equal; cbn [Z.to_nat skipn]; apply firstn_all2; rewrite length_le8; lia). }
  assert (KS3 : nk_kstate kbs1 = r_state R).
  { destruct (read_core_state tab (Some (x :: s')) 32 256 (nk_sent kbs) (nk_kstate kbs)) as (C1 & C2).
    apply kstate_of; [rewrite CH2; exact (eq_sym C1) | exact NX2 | rewrite EE2; exact (eq_sym C2)
                     | exact SK2 | exact SD2]. }
  zstep. zstep.
  assert (VC : V = 0 \/ V = 1 \/ V = 2 \/ V = 3) by exact (decide_cases _ _).
  destruct VC as [V0|[V1|[V2|V3]]].
  { (* MARK: reac_link_alias_write(ifname, "reac-pw:served") at 0x16530 *)
    rewrite V0. lit_branch. zstep. lit_branch.
    zstep. zstep. zstep. zstep.
    pose proof (wr_at_transport rsegs _ _ _ _ EW (wmono_trans rsegs _ _ _ WM2 WM3)) as EW3.
    assert (STRS : str_arg m3 66369 (Some link_spec.S_SERVED))
      by (split; [lia | split; [exact (served_at m3 MI3) | exact S_SERVED_no_nul]]).
    assert (LS : Z.of_nat (length link_spec.S_SERVED) = 14) by reflexivity.
    eapply (leaf_call _ _ _ _ _ HAW).
    { post_ext_tac. }
    { exact HQ. }
    { cbv beta. exists kbs1, tab, (Some (x :: s')), (Some link_spec.S_SERVED).
      rewrite ?mkR_a0, ?mkR_a1, ?mkR_errno. ulit.
      split; [exact NLK3|].
      split; [dj FAG ESP|].
      split; [exact WF2|]. split; [exact OPEN2|]. split; [lia|]. split; [lia|].
      split; [exact TAB3|].
      split; [exact EW3|].
      split; [dj EF ESP|].
      split; [exact EG|].
      split; [split; [exact A1N | exact NM3]|].
      split; [exact STRS|].
      split.
      { intros i n2 ix p Hi Hp.
        assert (Hi80 : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
        pose proof TAB as (_ & TL & _).
        assert (Hp0 : u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
        { apply (u64_back _ _ _ _ _ Hp MUf3). dj FAG TL Hi80 EG. }
        destruct (TOK i n2 ix p Hi Hp0) as (T1 & T2 & T3 & _).
        split; [dj T1 ESP|]. split; [exact T2 | exact T3]. }
      split. { intros sq Hs. injection Hs as Hs. subst sq. split; [dj SF ESP | dj SG]. }
      split.
      { intros sq Hs. injection Hs as Hs. subst sq. rewrite LS.
        split; [dj ESP ITOP LO | unfold apart_gnl, A_G_NL, NK_SIZE; lia]. }
      intros sq Hs. injection Hs as Hs. subst sq. rewrite LS. exists [].
      split; [apply bytes_at_nil; lia | cbn [length Z.of_nat]; lia]. }
    { exact MI3. }
    { rewrite ESP. exact ST3. }
    { rewrite ESP. lia. }
    { rewrite ESP. lia. }
    intros ra6 t06 t16 t26 a06 a16 a26 a36 a46 a56 a66 a76 t36 t46 t56 t66 m6 MU6 WM6 MI6 ST6 PO6.
    cbv beta in PO6, MU6. rewrite ?mkR_errno in MU6. rewrite ESP in MU6, ST6.
    rewrite ?mkR_a0, ?mkR_a1 in PO6. rewrite (unsigned_lit 66369) in PO6 by lia.
    specialize (PO6 kbs1 tab (Some (x :: s')) (Some link_spec.S_SERVED) NLK3 TAB3 (conj A1N NM3) STRS).
    rewrite SENT2, KS3 in PO6.
    set (W := write_lib tab (Some (x :: s')) (Some link_spec.S_SERVED) (r_reqs R) (r_state R)) in *.
    destruct PO6 as (RC6 & (kbs2 & NLK6 & WF6 & CH6 & EE6 & NIF6 & TAB6 & NX6 & SK6 & SD6 & SENT6 & NSENT6
                    & OPEN6 & MIS6 & OC6 & OB6 & OZ6)).
    assert (EA6 : a06 = wz (w_rc W)) by exact RC6. subst a06. clear RC6.
    assert (WCR : - 2 ^ 31 <= w_rc W < 2 ^ 31).
    { destruct (kstate_bounds kbs1 WF2) as (B1 & B2 & B3). rewrite KS3 in B1, B2, B3.
      exact (write_rc_range _ _ _ _ _ B1 B2 B3). }
    rewrite ret_pc_even by (lia || reflexivity).
    assert (MUf6 : munch [(bv_unsigned sp - 17248, bv_unsigned sp); (A_G_NL, A_G_NL + NK_N_SENT + 4);
       (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4)] m m6).
    { apply (munch_trans _ m m3 m6 MUf3). eapply munch_weaken; [|exact MU6].
      intros y Hy. cbn [outside] in *. destruct Hy as (H1 & H2 & H3 & _).
      repeat split; try exact I; try assumption; lia. }
    pose proof (wmono_trans rsegs m m3 m6 WMf3 WM6) as WMf6.
    assert (FRS6 : rw_cells rsegs m6 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply (rw_cells_transport rsegs _ m3 m6 _ _ FRS3 MU6 WM6); cbn [cells_size csize Nat.add]; dj FAG EF).
    assert (FRK6 : rw_cells rsegs m6 (bv_unsigned sp + -64) [CB (Z.to_nat 32) jk2])
      by (apply (rw_cells_transport rsegs _ m3 m6 _ _ FRK3 MU6 WM6); cbn [cells_size csize Nat.add]; dj FAG EF).
    assert (FRB6 : rw_cells rsegs m6 (bv_unsigned sp + -320) [CB (Z.to_nat 256) jb2])
      by (apply (rw_cells_transport rsegs _ m3 m6 _ _ FRB3 MU6 WM6); cbn [cells_size csize Nat.add]; dj FAG EF).
    assert (TM6 : task_mem rsegs m6) by exact (task_mem_munch _ _ _ TM MUf6 TASKW).
    assert (MF6 : memfile_k m6 sink k) by exact (memfile_k_transport _ _ _ _ _ MF MUf6 WMf6 MFD).
    assert (GG6 : bytes_at rsegs m6 A_GOT_GUARD (le8 (wz A_GUARD))).
    { apply (bytes_at_transport rsegs _ _ _ _ _ (proj1 GW) MUf6). rewrite length_le8. dj EGG ITOP LO. }
    assert (NM6 : cstr_at m6 (bv_unsigned a1) (x :: s')).
    { apply (cstr_transport _ _ _ _ _ CS MUf6). dj SF SG SE. }
    assert (SL6 : bytes_at rsegs m6 (bv_unsigned a1 + Z.of_nat (length (x :: s')) + 1) slack).
    { apply (bytes_at_transport rsegs _ _ _ _ _ SLB MUf6). dj SF SG SE SLL. }
    pose proof (marks_transport _ _ _ _ _ GBS MUf6 WMf6 MKD) as G6.
    clear FRS3 FRK3 FRB3 MU6.
    zstep. unfold wz. rewrite bv_eqb_z0 by lia.
    destruct (Z.eqb_spec (w_rc W) 0) as [W0|WN]; cbv iota.
    { (* 0x16604: marked; remember(m, ifname) at 0x1660c, answer 0 *)
      zstep. zstep. zstep.
      match goal with |- evt _ _ (MS ?Rg _ _ _ _ _ _) =>
        assert (SPR : spZ Rg = bv_unsigned sp + -320)
          by (unfold spZ; change (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -320)) = bv_unsigned sp + -320);
              exact ESP);
        assert (RMP : rm_pre Rg m6)
          by (apply (remember_pre Rg m6 gbs (x :: s') slack);
              try change (arg Rg 0) with (bv_unsigned a0); try change (arg Rg 1) with (bv_unsigned a1);
              [exact G6 | exact GWF | exact A1N | exact NM6 | exact SL | exact MI6 | exact SM | exact MKI
              | exact SL6 | exact SLL | dj MKF SPR | dj SF SPR])
      end.
      eapply (leaf_fp_call _ _ _ _ _ HRM).
      { post_ext_tac. }
      { exact HQ. }
      { exact RMP. }
      { exact MI6. }
      { exact TM6. }
      { rewrite ESP. exact ST6. }
      { rewrite ESP. lia. }
      { rewrite ESP. lia. }
      { exact FRM. }
      { exact ITOP. }
      { exact GG6. }
      { exact (guard_any m6). }
      intros ra7 t07 t17 t27 a07 a17 a27 a37 a47 a57 a67 a77 t37 t47 t57 t67 Ft7 fc7 m7
        FRM7 FK7 MU7 WM7 MI7 TM7 ST7 PO7.
      cbv beta in PO7, MU7. rewrite ?mkR_a0, ?mkR_a1 in PO7, MU7. rewrite ESP in MU7, ST7.
      destruct (PO7 gbs (x :: s') G6 NM6) as (gbs' & G7 & GW7 & GN7 & GL7). clear PO7.
      rewrite ret_pc_even by (lia || reflexivity).
      assert (FRS7 : rw_cells rsegs m7 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
        by (apply (rw_cells_transport rsegs _ m6 m7 _ _ FRS6 MU7 WM7); cbn [cells_size csize Nat.add]; dj MKF).
      assert (FRK7 : rw_cells rsegs m7 (bv_unsigned sp + -64) [CB (Z.to_nat 32) jk2])
        by (apply (rw_cells_transport rsegs _ m6 m7 _ _ FRK6 MU7 WM7); cbn [cells_size csize Nat.add]; dj MKF).
      assert (FRB7 : rw_cells rsegs m7 (bv_unsigned sp + -320) [CB (Z.to_nat 256) jb2])
        by (apply (rw_cells_transport rsegs _ m6 m7 _ _ FRB6 MU7 WM7); cbn [cells_size csize Nat.add]; dj MKF).
      zstep. zstep. exit7.
      release_frame FRB7 ST7 (bv_unsigned sp + -64). release_frame FRK7 ST7 (bv_unsigned sp + -32).
      release_frame FRS7 ST7 (bv_unsigned sp).
      fin_start.
      split.
      { apply (munch_trans _ m m6 m7).
        - eapply munch_weaken; [|exact MUf6]. intros y Hy. unfold mf_block in Hy. cbn [outside] in *. tauto.
        - eapply munch_weaken; [|exact MU7]. intros y Hy. unfold mf_block in Hy. cbn [outside fst snd] in *.
          destruct Hy as (H1 & H2 & H3 & H4 & H5 & _).
          repeat split; try exact I; try assumption; lia. }
      split; [exact (wmono_trans rsegs m m6 m7 WMf6 WM7)|]. split; [exact MI7|]. split; [exact TM7|].
      split; [exact ST7|].
      split.
      { intros k0 Hk. rewrite (memfile_k_unique _ _ _ _ Hk MF). exists k.
        split; [unfold MARK_LINE_MAX; lia|].
        apply (memfile_k_transport _ _ _ _ _ MF6 MU7 WM7). dj SNB MKS. }
      split. { intros Hc. exfalso. exact (A0N Hc). }
      intros _.
      refine (post_marks_of m m7 _ _ kbs tab (Some (x :: s')) gbs _
                (Mres 0 (remember (mk_names gbs) (x :: s')) (w_reqs W) (w_state W)) kbs2 gbs' NLK TAB
                (conj A1N CS) GBS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      + rewrite mark_lib_some. cbv zeta.
        change (read_core tab (Some (x :: s')) 32 256 (nk_sent kbs) (nk_kstate kbs)) with R.
        change (decide (Some (r_kind R)) (Some (r_alias R))) with V.
        replace (r_rc R =? 0) with true by (symmetry; apply Z.eqb_eq; exact RC0).
        rewrite V0.
        change (write_core tab (Some (x :: s')) (Some link_spec.S_SERVED) (r_reqs R) (r_state R)) with W.
        replace (w_rc W =? 0) with true by (symmetry; apply Z.eqb_eq; exact W0).
        reflexivity.
      + reflexivity.
      + exact G7.
      + exact GW7.
      + exact GN7.
      + apply (nlk_transport _ _ _ _ NLK6 MU7 WM7). dj FAG MKG.
      + exact WF6.
      + rewrite CH6; exact CH2.
      + rewrite EE6; exact EE2.
      + rewrite NIF6; exact NIF2.
      + apply (iftab_transport _ _ _ _ _ TAB6 MU7); [dj FAG MKG|].
        intros i n2 ix p Hi Hp.
        assert (Hi80 : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
        pose proof TAB as (_ & TL & _).
        assert (Hp0 : u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
        { apply (u64_back _ _ _ _ _ Hp MUf6). dj FAG TL Hi80 EG. }
        destruct (TOK i n2 ix p Hi Hp0) as (T1 & _ & _ & _ & T5). specialize (T5 A0N). dj T1 T5.
      + exact NX6.
      + exact SENT6.
      + exact NSENT6.
      + exact OPEN6.
      + rewrite MIS6; exact MIS2.
      + lia.
      + lia. }
    (* 0x16538: the write failed; say() is g_say; the cap by rc = -EPERM at 0x1655c *)
    assert (HRS6 : ov_read_bytes rsegs m6 (Z_to_bv 64 480560) 8 = Some (le8 (Z_to_bv 64 sink))).
    { assert (SAY6 : bytes_at rsegs m6 480560 (le8 (Z_to_bv 64 sink))).
      { apply (bytes_at_transport rsegs _ _ _ _ _ SAY MUf6). rewrite length_le8. dj ESAY ITOP LO. }
      pose proof (bytes_at_read rsegs m6 480560 (le8 (Z_to_bv 64 sink)) 0 8 SAY6 ltac:(lia)
                    ltac:(rewrite length_le8; cbn; lia)) as H.
      rewrite Z.add_0_r in H. unfold wa in H. rewrite H.
      try (f_equal; cbn [Z.to_nat skipn]; apply firstn_all2; rewrite length_le8; lia). }
    zstep. zstep. zstep. zstep.
    rewrite SKE. cbn [negb]. cbv iota.
    zstep. zstep. zstep.
    destruct (bv_eqb (Z_to_bv 64 (w_rc W)) (Z_to_bv 64 (-1))); cbv iota;
      [ zstep; zstep; pose proof s_cap_ok as CAPOK;
        pose proof (or_introl (@eq_refl _ S_CAP) : S_CAP = S_CAP \/ S_CAP = S_EMPTY) as CAPC
      | zstep; zstep; zstep; pose proof s_empty_ok as CAPOK;
        pose proof (or_intror (@eq_refl _ S_EMPTY) : S_EMPTY = S_CAP \/ S_EMPTY = S_EMPTY) as CAPC ].
    (* from 0x16620 the two arms differ only in a7, the cap: reac_code_emit at 0x16638, then the exit *)
    all: (
  zstep; zstep; zstep; zstep; zstep; zstep; zstep;
  match goal with |- evt _ _ (MS ?Rg _ _ _ _ _ _) =>
    let A0R := fresh "A0R" in let A3R := fresh "A3R" in let G15 := fresh "G15" in
    let G17 := fresh "G17" in let SPR := fresh "SPR" in let NO := fresh "NO" in
    assert (A0R : arg Rg 0 = sink)
      by (unfold arg; change (bv_unsigned (Z_to_bv 64 sink) = sink); apply unsigned_lit; lia);
    assert (A3R : arg Rg 3 = FMT_MARK_A) by (unfold arg; reflexivity);
    assert (G15 : getr Rg 15 = Z_to_bv 64 S_SERVED_A) by reflexivity;
    match type of CAPOK with str_ok ?cA _ _ => assert (G17 : getr Rg 17 = Z_to_bv 64 cA) by reflexivity end;
    assert (SPR : spZ Rg = bv_unsigned sp + -320)
      by (unfold spZ; change (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -320)) = bv_unsigned sp + -320);
          exact ESP);
    assert (NO : name_ok m6 (getr Rg 14) (x :: s') (spZ Rg) (spZ Rg - 6112) sink)
      by (change (getr Rg 14) with a1; rewrite SPR; unfold name_ok;
          split; [exact NM6|]; split; [exact A1N|]; split; [exact SL|];
          split; [exists slack; split; [exact SL6 | exact SLL]|]; split; [dj SF ESP | dj SS]);
    destruct (mark_emit Rg m6 sink k (x :: s') _ _ _ A0R A3R G15 G17 CAPOK CAPC MI6 MF6 MFK SNZ
                ltac:(rewrite SPR; unfold FILE_BLOCK in *; lia)
                ltac:(rewrite SPR; unfold RO_END, A_IMG_TOP in *; lia) MFP NO)
      as (eargs & T & EFM & LT & CPRE)
  end;
  eapply (leaf_fp_call _ _ _ _ _ HCE);
  [ post_ext_tac | exact HQ | exact CPRE | exact MI6 | exact TM6 | rewrite ESP; exact ST6
  | rewrite ESP; lia | rewrite ESP; lia | exact FRM | exact ITOP | exact GG6 | exact (guard_any m6) | ];
  intros ra7 t07 t17 t27 a07 a17 a27 a37 a47 a57 a67 a77 t37 t47 t57 t67 Ft7 fc7 m7
    FRM7 FK7 MU7 WM7 MI7 TM7 ST7 PO7;
  cbv beta in PO7, MU7; rewrite ?mkR_a0 in PO7, MU7; rewrite (unsigned_lit sink) in PO7, MU7 by lia;
  rewrite ESP in MU7, ST7;
  pose proof (PO7 _ _ _ _ _ EFM MF6) as MF7; clear PO7;
  rewrite ret_pc_even by (lia || reflexivity);
  unfold mf_block in MU7; cbn [fst snd] in MU7;
  assert (FRS7 : rw_cells rsegs m7 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
    by (apply (rw_cells_transport rsegs _ m6 m7 _ _ FRS6 MU7 WM7); cbn [cells_size csize Nat.add]; dj SNB);
  assert (FRK7 : rw_cells rsegs m7 (bv_unsigned sp + -64) [CB (Z.to_nat 32) jk2])
    by (apply (rw_cells_transport rsegs _ m6 m7 _ _ FRK6 MU7 WM7); cbn [cells_size csize Nat.add]; dj SNB);
  assert (FRB7 : rw_cells rsegs m7 (bv_unsigned sp + -320) [CB (Z.to_nat 256) jb2])
    by (apply (rw_cells_transport rsegs _ m6 m7 _ _ FRB6 MU7 WM7); cbn [cells_size csize Nat.add]; dj SNB);
  zstep; exit7;
  release_frame FRB7 ST7 (bv_unsigned sp + -64); release_frame FRK7 ST7 (bv_unsigned sp + -32);
  release_frame FRS7 ST7 (bv_unsigned sp);
  fin_start;
  split;
  [ apply (munch_trans _ m m6 m7);
    [ eapply munch_weaken; [|exact MUf6]; intros y Hy; unfold mf_block in Hy; cbn [outside] in *; tauto
    | eapply munch_weaken; [|exact MU7]; intros y Hy; unfold mf_block in Hy; cbn [outside fst snd] in *;
      destruct Hy as (H1 & H2 & H3 & H4 & H5 & _); repeat split; try exact I; try assumption; lia ]
  | ];
  split; [exact (wmono_trans rsegs m m6 m7 WMf6 WM7)|]; split; [exact MI7|]; split; [exact TM7|];
  split; [exact ST7|];
  split;
  [ intros k0 Hk; rewrite (memfile_k_unique _ _ _ _ Hk MF); exists (k + EMIT_HEAD + Z.of_nat (length T));
    split; [unfold EMIT_HEAD, MARK_LINE_MAX in *; lia | exact MF7] | ];
  split; [intros Hc; exfalso; exact (A0N Hc)|];
  intros _;
  refine (post_marks_of m m7 _ _ kbs tab (Some (x :: s')) gbs _
            (Mres (w_rc W) (mk_names gbs) (w_reqs W) (w_state W)) kbs2 gbs NLK TAB (conj A1N CS) GBS
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
  [ rewrite mark_lib_some; cbv zeta;
    change (read_core tab (Some (x :: s')) 32 256 (nk_sent kbs) (nk_kstate kbs)) with R;
    change (decide (Some (r_kind R)) (Some (r_alias R))) with V;
    replace (r_rc R =? 0) with true by (symmetry; apply Z.eqb_eq; exact RC0);
    rewrite V0;
    change (write_core tab (Some (x :: s')) (Some link_spec.S_SERVED) (r_reqs R) (r_state R)) with W;
    replace (w_rc W =? 0) with false by (symmetry; apply Z.eqb_neq; exact WN);
    reflexivity
  | reflexivity
  | apply (marks_transport _ _ _ _ _ G6 MU7 WM7); dj MKF MKS
  | exact GWF
  | reflexivity
  | apply (nlk_transport _ _ _ _ NLK6 MU7 WM7); dj FAG MFP
  | exact WF6
  | rewrite CH6; exact CH2
  | rewrite EE6; exact EE2
  | rewrite NIF6; exact NIF2
  | apply (iftab_transport _ _ _ _ _ TAB6 MU7); [dj FAG MFP|];
    let i := fresh "i" in let n2 := fresh "n2" in let ix := fresh "ix" in let p := fresh "p" in
    let Hi := fresh "Hi" in let Hp := fresh "Hp" in
    intros i n2 ix p Hi Hp;
    let Hi80 := fresh "Hi80" in let TL := fresh "TL" in let Hp0 := fresh "Hp0" in
    assert (Hi80 : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate);
    pose proof TAB as (_ & TL & _);
    assert (Hp0 : u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p)
      by (apply (u64_back _ _ _ _ _ Hp MUf6); dj FAG TL Hi80 EG);
    let T1 := fresh "T1" in let T4 := fresh "T4" in
    destruct (TOK i n2 ix p Hi Hp0) as (T1 & _ & _ & T4 & _); dj T1 T4
  | exact NX6
  | exact SENT6
  | exact NSENT6
  | exact OPEN6
  | rewrite MIS6; exact MIS2
  | lia
  | lia ]).
  }
  { (* OURS: bcmp(alias, "reac-pw:served", 15) at 0x165b4; equal: remember at 0x165c8; answer 1 *)
    rewrite V1. lit_branch. zstep. lit_branch.
    zstep. zstep. zstep. zstep. zstep.
    destruct (cb_bytes _ _ _ _ FRB3) as (BB & LBB).
    assert (LAL : Z.of_nat (length (r_alias R)) <= 255) by (apply read_alias_len; lia).
    assert (PRB : firstn (S (length (r_alias R))) jb2 = r_alias R ++ [zb 0])
      by (apply (cstr_prefix m3 _ _ _ ALIAS3 BB); rewrite LBB; change (Z.to_nat 256) with 256%nat; lia).
    destruct (bcmp_served (r_alias R) jb2 (proj2 ALIAS3) PRB
                ltac:(rewrite LBB; change (Z.to_nat 256) with 256%nat; lia))
      as (v & MV & RV & IV).
    eapply evt_cut.
    { eapply HBC with (ls := jb2) (rs := link_spec.S_SERVED ++ [zb 0]) (v := v).
      - rewrite ESP. exact BB.
      - rewrite unsigned_lit by lia. exact (served_at m3 MI3).
      - exact MV.
      - exact MI3. }
    intros ms' (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m4
                & -> & MU4 & WM4 & MI4 & _ & _).
    rewrite ret_pc_even by (lia || reflexivity).
    assert (MUf4 : munch [(bv_unsigned sp - 17248, bv_unsigned sp); (A_G_NL, A_G_NL + NK_N_SENT + 4);
       (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4)] m m4)
      by (apply (munch_trans _ m m3 m4 MUf3); eapply munch_weaken; [|exact MU4]; intros y Hy; exact I).
    pose proof (wmono_trans rsegs m m3 m4 WMf3 WM4) as WMf4.
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ FRS3 MU4 WM4 I) as FRS4.
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ FRK3 MU4 WM4 I) as FRK4.
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ FRB3 MU4 WM4 I) as FRB4.
    pose proof (stk_transport_disjoint rsegs _ m3 m4 lo _ ST3 MU4 WM4 I) as ST4.
    pose proof (nlk_transport _ _ _ _ NLK3 MU4 WM4 I) as NLK4.
    assert (TAB4 : iftab_at m4 kbs1 tab)
      by (apply (iftab_transport _ _ _ _ _ TAB3 MU4 I); intros; exact I).
    pose proof (bytes_at_transport rsegs _ _ _ _ _ GG3 MU4 I) as GG4.
    pose proof (cstr_transport _ _ _ _ _ NM3 MU4 I) as NM4.
    pose proof (bytes_at_transport rsegs _ _ _ _ _ SL3 MU4 I) as SL4.
    assert (TM4 : task_mem rsegs m4) by exact (task_mem_munch _ _ _ TM MUf4 TASKW).
    pose proof (marks_transport _ _ _ _ _ GBS MUf4 WMf4 MKD) as G4.
    clear FRS3 FRK3 FRB3 ST3 NLK3 TAB3.
    zstep. zstep.
    rewrite bv_eqb_z0 by lia.
    destruct (Z.eqb_spec v 0) as [E0|N0]; cbn [negb]; cbv iota.
    2:{ (* 0x165bc: another alias of ours, answer 1 *)
      exit7.
      release_frame FRB4 ST4 (bv_unsigned sp + -64). release_frame FRK4 ST4 (bv_unsigned sp + -32).
      release_frame FRS4 ST4 (bv_unsigned sp).
      fin_start.
      split. { eapply munch_weaken; [|exact MUf4]. intros y Hy. unfold mf_block in Hy. cbn [outside] in *. tauto. }
      split; [exact WMf4|]. split; [exact MI4|]. split; [exact TM4|]. split; [exact ST4|].
      split.
      { intros k0 Hk. rewrite (memfile_k_unique _ _ _ _ Hk MF). exists k.
        split; [unfold MARK_LINE_MAX; lia | exact (memfile_k_transport _ _ _ _ _ MF MUf4 WMf4 MFD)]. }
      split. { intros Hc. exfalso. exact (A0N Hc). }
      intros _.
      refine (post_marks_of m m4 _ _ kbs tab (Some (x :: s')) gbs _
                (Mres 1 (mk_names gbs) (r_reqs R) (r_state R)) kbs1 gbs NLK TAB (conj A1N CS) GBS
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      + rewrite mark_lib_some. cbv zeta.
        change (read_core tab (Some (x :: s')) 32 256 (nk_sent kbs) (nk_kstate kbs)) with R.
        change (decide (Some (r_kind R)) (Some (r_alias R))) with V.
        replace (r_rc R =? 0) with true by (symmetry; apply Z.eqb_eq; exact RC0).
        rewrite V1.
        replace (bl_eqb (r_alias R) link_spec.S_SERVED) with false; [reflexivity|].
        symmetry. destruct (bl_eqb (r_alias R) link_spec.S_SERVED) eqn:EB; [|reflexivity].
        exfalso. apply N0. apply IV. apply bl_eqb_iff. exact EB.
      + reflexivity.
      + exact G4.
      + exact GWF.
      + reflexivity.
      + exact NLK4.
      + exact WF2.
      + exact CH2.
      + exact EE2.
      + exact NIF2.
      + exact TAB4.
      + exact NX2.
      + exact SENT2.
      + exact NSENT2.
      + exact OPEN2.
      + exact MIS2.
      + exact OC2.
      + lia. }
    (* 0x165c0: the served alias, remember(m, ifname) at 0x165c8 *)
    zstep. zstep. zstep.
    match goal with |- evt _ _ (MS ?Rg _ _ _ _ _ _) =>
      assert (SPR : spZ Rg = bv_unsigned sp + -320)
        by (unfold spZ; change (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -320)) = bv_unsigned sp + -320);
            exact ESP);
      assert (RMP : rm_pre Rg m4)
        by (apply (remember_pre Rg m4 gbs (x :: s') slack);
            try change (arg Rg 0) with (bv_unsigned a0); try change (arg Rg 1) with (bv_unsigned a1);
            [exact G4 | exact GWF | exact A1N | exact NM4 | exact SL | exact MI4 | exact SM | exact MKI
            | exact SL4 | exact SLL | dj MKF SPR | dj SF SPR])
    end.
    eapply (leaf_fp_call _ _ _ _ _ HRM).
    { post_ext_tac. }
    { exact HQ. }
    { exact RMP. }
    { exact MI4. }
    { exact TM4. }
    { rewrite ESP. exact ST4. }
    { rewrite ESP. lia. }
    { rewrite ESP. lia. }
    { exact FRM. }
    { exact ITOP. }
    { exact GG4. }
    { exact (guard_any m4). }
    intros ra5 t05 t15 t25 a05 a15 a25 a35 a45 a55 a65 a75 t35 t45 t55 t65 Ft5 fc5 m5
      FRM5 FK5 MU5 WM5 MI5 TM5 ST5 PO5.
    cbv beta in PO5, MU5. rewrite ?mkR_a0, ?mkR_a1 in PO5, MU5. rewrite ESP in MU5, ST5.
    destruct (PO5 gbs (x :: s') G4 NM4) as (gbs' & G5 & GW5 & GN5 & GL5). clear PO5.
    rewrite ret_pc_even by (lia || reflexivity).
    assert (FRS5 : rw_cells rsegs m5 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply (rw_cells_transport rsegs _ m4 m5 _ _ FRS4 MU5 WM5); cbn [cells_size csize Nat.add]; dj MKF).
    assert (FRK5 : rw_cells rsegs m5 (bv_unsigned sp + -64) [CB (Z.to_nat 32) jk2])
      by (apply (rw_cells_transport rsegs _ m4 m5 _ _ FRK4 MU5 WM5); cbn [cells_size csize Nat.add]; dj MKF).
    assert (FRB5 : rw_cells rsegs m5 (bv_unsigned sp + -320) [CB (Z.to_nat 256) jb2])
      by (apply (rw_cells_transport rsegs _ m4 m5 _ _ FRB4 MU5 WM5); cbn [cells_size csize Nat.add]; dj MKF).
    zstep. exit7.
    release_frame FRB5 ST5 (bv_unsigned sp + -64). release_frame FRK5 ST5 (bv_unsigned sp + -32).
    release_frame FRS5 ST5 (bv_unsigned sp).
    fin_start.
    split.
    { apply (munch_trans _ m m4 m5).
      - eapply munch_weaken; [|exact MUf4]. intros y Hy. unfold mf_block in Hy. cbn [outside] in *. tauto.
      - eapply munch_weaken; [|exact MU5]. intros y Hy. unfold mf_block in Hy. cbn [outside fst snd] in *.
        destruct Hy as (H1 & H2 & H3 & H4 & H5 & _).
        repeat split; try exact I; try assumption; lia. }
    split; [exact (wmono_trans rsegs m m4 m5 WMf4 WM5)|]. split; [exact MI5|]. split; [exact TM5|].
    split; [exact ST5|].
    split.
    { intros k0 Hk. rewrite (memfile_k_unique _ _ _ _ Hk MF). exists k.
      split; [unfold MARK_LINE_MAX; lia|].
      apply (memfile_k_transport _ _ _ _ _ (memfile_k_transport _ _ _ _ _ MF MUf4 WMf4 MFD) MU5 WM5).
      dj SNB MKS. }
    split. { intros Hc. exfalso. exact (A0N Hc). }
    intros _.
    refine (post_marks_of m m5 _ _ kbs tab (Some (x :: s')) gbs _
              (Mres 1 (remember (mk_names gbs) (x :: s')) (r_reqs R) (r_state R)) kbs1 gbs' NLK TAB
              (conj A1N CS) GBS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + rewrite mark_lib_some. cbv zeta.
      change (read_core tab (Some (x :: s')) 32 256 (nk_sent kbs) (nk_kstate kbs)) with R.
      change (decide (Some (r_kind R)) (Some (r_alias R))) with V.
      replace (r_rc R =? 0) with true by (symmetry; apply Z.eqb_eq; exact RC0).
      rewrite V1.
      replace (bl_eqb (r_alias R) link_spec.S_SERVED) with true
        by (symmetry; apply bl_eqb_iff; apply IV; exact E0).
      reflexivity.
    + reflexivity.
    + exact G5.
    + exact GW5.
    + exact GN5.
    + apply (nlk_transport _ _ _ _ NLK4 MU5 WM5). dj FAG MKG.
    + exact WF2.
    + exact CH2.
    + exact EE2.
    + exact NIF2.
    + apply (iftab_transport _ _ _ _ _ TAB4 MU5); [dj FAG MKG|].
      intros i n2 ix p Hi Hp.
      assert (Hi80 : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      pose proof TAB as (_ & TL & _).
      assert (Hp0 : u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
      { apply (u64_back _ _ _ _ _ Hp MUf4). dj FAG TL Hi80 EG. }
      destruct (TOK i n2 ix p Hi Hp0) as (T1 & _ & _ & _ & T5). specialize (T5 A0N). dj T1 T5.
    + exact NX2.
    + exact SENT2.
    + exact NSENT2.
    + exact OPEN2.
    + exact MIS2.
    + exact OC2.
    + lia. }
  { (* LEAVE_VLAN: fprintf(say(), 0x102b3, ifname) at 0x16598, answer 2 *)
    rewrite V2. lit_branch. zstep. zstep. lit_branch. zstep. zstep. zstep.
    rewrite SKE. cbn [negb]. cbv iota.
    zstep. zstep. zstep. zstep.
    match goal with |- evt _ _ (MS ?Rg _ _ _ _ _ _) =>
      assert (A0R : arg Rg 0 = sink)
        by (unfold arg; change (bv_unsigned (Z_to_bv 64 sink) = sink); apply unsigned_lit; lia);
      assert (A1R : arg Rg 1 = FMT_VLAN_A) by (unfold arg; reflexivity);
      assert (SPR : spZ Rg = bv_unsigned sp + -320)
        by (unfold spZ; change (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -320)) = bv_unsigned sp + -320);
            exact ESP);
      assert (NO : name_ok m3 (getr Rg 12) (x :: s') (spZ Rg) (spZ Rg - FPRINTF_K) sink)
        by (change (getr Rg 12) with a1; rewrite SPR; unfold name_ok, FPRINTF_K;
            split; [exact NM3|]; split; [exact A1N|]; split; [exact SL|];
            split; [exists slack; split; [exact SL3 | exact SLL]|]; split; [dj SF | dj SS]);
      destruct (vlan_pre Rg m3 sink k (x :: s') A0R A1R MI3 MF3 MFK
                  ltac:(rewrite SPR; unfold FPRINTF_K, FILE_BLOCK, MemFile.MF_BLOCK in *; lia)
                  ltac:(rewrite SPR; unfold FPRINTF_K, IMG_TOP, A_IMG_TOP in *; lia) GW3 NO)
        as (fl & om & wend & wpos & wbase & pos & len & pb & T & LT & FPRE)
    end.
    eapply (leaf_fp_call _ _ _ _ _
              (HFP sink k fl om wend wpos wbase pos len pb FMT_VLAN PS_VLAN [APtr (map bv_unsigned (x :: s'))] T)).
    { post_ext_tac. }
    { exact HQ. }
    { exact FPRE. }
    { exact MI3. }
    { exact TM3. }
    { rewrite ESP. exact ST3. }
    { rewrite ESP. unfold FPRINTF_K. lia. }
    { rewrite ESP. lia. }
    { exact FRM. }
    { exact ITOP. }
    { exact GG3. }
    { exact (guard_any m3). }
    intros ra5 t05 t15 t25 a05 a15 a25 a35 a45 a55 a65 a75 t35 t45 t55 t65 Ft5 fc5 m4
      FRM5 FK5 MU5 WM5 MI5 TM5 ST5 PO5.
    cbv beta in PO5, MU5. destruct PO5 as [_ (MF5 & _ & _)].
    rewrite ESP in MU5, ST5. unfold mf_block in MU5. cbn [fst snd] in MU5.
    rewrite ret_pc_even by (lia || reflexivity).
    assert (FRS5 : rw_cells rsegs m4 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply (rw_cells_transport rsegs _ m3 m4 _ _ FRS3 MU5 WM5); cbn [cells_size csize Nat.add];
          unfold FPRINTF_K; dj SNB).
    assert (FRK5 : rw_cells rsegs m4 (bv_unsigned sp + -64) [CB (Z.to_nat 32) jk2])
      by (apply (rw_cells_transport rsegs _ m3 m4 _ _ FRK3 MU5 WM5); cbn [cells_size csize Nat.add];
          unfold FPRINTF_K; dj SNB).
    assert (FRB5 : rw_cells rsegs m4 (bv_unsigned sp + -320) [CB (Z.to_nat 256) jb2])
      by (apply (rw_cells_transport rsegs _ m3 m4 _ _ FRB3 MU5 WM5); cbn [cells_size csize Nat.add];
          unfold FPRINTF_K; dj SNB).
    zstep. zstep. exit7.
    release_frame FRB5 ST5 (bv_unsigned sp + -64). release_frame FRK5 ST5 (bv_unsigned sp + -32).
    release_frame FRS5 ST5 (bv_unsigned sp).
    fin_start.
    split.
    { apply (munch_trans _ m m3 m4).
      - eapply munch_weaken; [|exact MUf3]. intros y Hy. unfold mf_block in Hy. cbn [outside] in *. tauto.
      - eapply munch_weaken; [|exact MU5]. intros y Hy. unfold mf_block in Hy. cbn [outside fst snd] in *.
        destruct Hy as (H1 & H2 & H3 & H4 & H5 & _). unfold FPRINTF_K.
        repeat split; try exact I; try assumption; lia. }
    split; [exact (wmono_trans rsegs m m3 m4 WMf3 WM5)|]. split; [exact MI5|]. split; [exact TM5|].
    split; [exact ST5|].
    split.
    { intros k0 Hk. rewrite (memfile_k_unique _ _ _ _ Hk MF). exists (k + Z.of_nat (length T)).
      split; [unfold MARK_LINE_MAX in *; lia | exact MF5]. }
    split. { intros Hc. exfalso. exact (A0N Hc). }
    intros _.
    refine (post_marks_of m m4 _ _ kbs tab (Some (x :: s')) gbs _
              (Mres 2 (mk_names gbs) (r_reqs R) (r_state R)) kbs1 gbs NLK TAB (conj A1N CS) GBS
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + rewrite mark_lib_some. cbv zeta.
      change (read_core tab (Some (x :: s')) 32 256 (nk_sent kbs) (nk_kstate kbs)) with R.
      change (decide (Some (r_kind R)) (Some (r_alias R))) with V.
      replace (r_rc R =? 0) with true by (symmetry; apply Z.eqb_eq; exact RC0).
      rewrite V2. reflexivity.
    + reflexivity.
    + apply (marks_transport _ _ _ _ _ (marks_transport _ _ _ _ _ GBS MUf3 WMf3 MKD) MU5 WM5).
      unfold FPRINTF_K. dj MKF MKS.
    + exact GWF.
    + reflexivity.
    + apply (nlk_transport _ _ _ _ NLK3 MU5 WM5). unfold FPRINTF_K. dj FAG MFP.
    + exact WF2.
    + exact CH2.
    + exact EE2.
    + exact NIF2.
    + apply (iftab_transport _ _ _ _ _ TAB3 MU5); [unfold FPRINTF_K; dj FAG MFP|].
      intros i n2 ix p Hi Hp.
      assert (Hi80 : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      pose proof TAB as (_ & TL & _).
      assert (Hp0 : u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
      { apply (u64_back _ _ _ _ _ Hp MUf3). dj FAG TL Hi80 EG. }
      destruct (TOK i n2 ix p Hi Hp0) as (T1 & _ & _ & T4 & _). unfold FPRINTF_K. dj T1 T4.
    + exact NX2.
    + exact SENT2.
    + exact NSENT2.
    + exact OPEN2.
    + exact MIS2.
    + exact OC2.
    + lia. }
  { (* LEAVE_HOST: fprintf(say(), 0x1049d, ifname, alias) at 0x165f8, answer 3 *)
    rewrite V3. lit_branch. zstep. zstep. lit_branch. zstep. zstep. zstep.
    rewrite SKE. cbn [negb]. cbv iota.
    zstep. zstep. zstep. zstep. zstep.
    destruct (cb_bytes _ _ _ _ FRB3) as (BB & LBB). destruct (cb_bytes _ _ _ _ FRK3) as (BK & LBK).
    assert (BIG : bytes_at rsegs m3 (bv_unsigned sp + -320) (jb2 ++ jk2)).
    { apply (proj2 (bytes_at_app rsegs m3 _ jb2 jk2)). split; [exact BB|].
      rewrite LBB. replace (bv_unsigned sp + -320 + Z.of_nat (Z.to_nat 256)) with (bv_unsigned sp + -64)
        by (cbn; lia). exact BK. }
    assert (LAL : Z.of_nat (length (r_alias R)) <= 255) by (apply read_alias_len; lia).
    assert (LBIG : length (jb2 ++ jk2) = 288%nat) by (rewrite length_app, LBB, LBK; reflexivity).
    assert (PRB : firstn (S (length (r_alias R))) (jb2 ++ jk2) = r_alias R ++ [zb 0])
      by (apply (cstr_prefix m3 _ _ _ ALIAS3 BIG); rewrite LBIG; lia).
    match goal with |- evt _ _ (MS ?Rg _ _ _ _ _ _) =>
      assert (A0R : arg Rg 0 = sink)
        by (unfold arg; change (bv_unsigned (Z_to_bv 64 sink) = sink); apply unsigned_lit; lia);
      assert (A1R : arg Rg 1 = FMT_HOST_A) by (unfold arg; reflexivity);
      assert (SPR : spZ Rg = bv_unsigned sp + -320)
        by (unfold spZ; change (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -320)) = bv_unsigned sp + -320);
            exact ESP);
      assert (G13 : bv_unsigned (getr Rg 13) = bv_unsigned sp + -320)
        by (change (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -320)) = bv_unsigned sp + -320); exact ESP);
      assert (NO : name_ok m3 (getr Rg 12) (x :: s') (spZ Rg) (spZ Rg - FPRINTF_K) sink)
        by (change (getr Rg 12) with a1; rewrite SPR; unfold name_ok, FPRINTF_K;
            split; [exact NM3|]; split; [exact A1N|]; split; [exact SL|];
            split; [exists slack; split; [exact SL3 | exact SLL]|]; split; [dj SF | dj SS]);
      destruct (host_pre Rg m3 sink k (x :: s') (r_alias R) (jb2 ++ jk2) A0R A1R MI3 MF3 MFK
                  ltac:(rewrite SPR; unfold FPRINTF_K, FILE_BLOCK, MemFile.MF_BLOCK in *; lia)
                  ltac:(rewrite SPR; unfold FPRINTF_K, IMG_TOP, A_IMG_TOP in *; lia) GW3 NO
                  (proj2 ALIAS3) LAL ltac:(rewrite G13; exact BIG) PRB ltac:(rewrite LBIG; lia)
                  ltac:(rewrite G13; lia) ltac:(rewrite G13, SPR; lia)
                  ltac:(rewrite G13; unfold FILE_BLOCK, MemFile.MF_BLOCK in *; lia))
        as (fl & om & wend & wpos & wbase & pos & len & pb & T & LT & FPRE)
    end.
    eapply (leaf_fp_call _ _ _ _ _
              (HFP sink k fl om wend wpos wbase pos len pb FMT_HOST PS_HOST
                 [APtr (map bv_unsigned (x :: s')); APtr (map bv_unsigned (r_alias R))] T)).
    { post_ext_tac. }
    { exact HQ. }
    { exact FPRE. }
    { exact MI3. }
    { exact TM3. }
    { rewrite ESP. exact ST3. }
    { rewrite ESP. unfold FPRINTF_K. lia. }
    { rewrite ESP. lia. }
    { exact FRM. }
    { exact ITOP. }
    { exact GG3. }
    { exact (guard_any m3). }
    intros ra5 t05 t15 t25 a05 a15 a25 a35 a45 a55 a65 a75 t35 t45 t55 t65 Ft5 fc5 m4
      FRM5 FK5 MU5 WM5 MI5 TM5 ST5 PO5.
    cbv beta in PO5, MU5. destruct PO5 as [_ (MF5 & _ & _)].
    rewrite ESP in MU5, ST5. unfold mf_block in MU5. cbn [fst snd] in MU5.
    rewrite ret_pc_even by (lia || reflexivity).
    assert (FRS5 : rw_cells rsegs m4 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply (rw_cells_transport rsegs _ m3 m4 _ _ FRS3 MU5 WM5); cbn [cells_size csize Nat.add];
          unfold FPRINTF_K; dj SNB).
    assert (FRK5 : rw_cells rsegs m4 (bv_unsigned sp + -64) [CB (Z.to_nat 32) jk2])
      by (apply (rw_cells_transport rsegs _ m3 m4 _ _ FRK3 MU5 WM5); cbn [cells_size csize Nat.add];
          unfold FPRINTF_K; dj SNB).
    assert (FRB5 : rw_cells rsegs m4 (bv_unsigned sp + -320) [CB (Z.to_nat 256) jb2])
      by (apply (rw_cells_transport rsegs _ m3 m4 _ _ FRB3 MU5 WM5); cbn [cells_size csize Nat.add];
          unfold FPRINTF_K; dj SNB).
    zstep. zstep. exit7.
    release_frame FRB5 ST5 (bv_unsigned sp + -64). release_frame FRK5 ST5 (bv_unsigned sp + -32).
    release_frame FRS5 ST5 (bv_unsigned sp).
    fin_start.
    split.
    { apply (munch_trans _ m m3 m4).
      - eapply munch_weaken; [|exact MUf3]. intros y Hy. unfold mf_block in Hy. cbn [outside] in *. tauto.
      - eapply munch_weaken; [|exact MU5]. intros y Hy. unfold mf_block in Hy. cbn [outside fst snd] in *.
        destruct Hy as (H1 & H2 & H3 & H4 & H5 & _). unfold FPRINTF_K.
        repeat split; try exact I; try assumption; lia. }
    split; [exact (wmono_trans rsegs m m3 m4 WMf3 WM5)|]. split; [exact MI5|]. split; [exact TM5|].
    split; [exact ST5|].
    split.
    { intros k0 Hk. rewrite (memfile_k_unique _ _ _ _ Hk MF). exists (k + Z.of_nat (length T)).
      split; [unfold MARK_LINE_MAX in *; lia | exact MF5]. }
    split. { intros Hc. exfalso. exact (A0N Hc). }
    intros _.
    refine (post_marks_of m m4 _ _ kbs tab (Some (x :: s')) gbs _
              (Mres 3 (mk_names gbs) (r_reqs R) (r_state R)) kbs1 gbs NLK TAB (conj A1N CS) GBS
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + rewrite mark_lib_some. cbv zeta.
      change (read_core tab (Some (x :: s')) 32 256 (nk_sent kbs) (nk_kstate kbs)) with R.
      change (decide (Some (r_kind R)) (Some (r_alias R))) with V.
      replace (r_rc R =? 0) with true by (symmetry; apply Z.eqb_eq; exact RC0).
      rewrite V3. reflexivity.
    + reflexivity.
    + apply (marks_transport _ _ _ _ _ (marks_transport _ _ _ _ _ GBS MUf3 WMf3 MKD) MU5 WM5).
      unfold FPRINTF_K. dj MKF MKS.
    + exact GWF.
    + reflexivity.
    + apply (nlk_transport _ _ _ _ NLK3 MU5 WM5). unfold FPRINTF_K. dj FAG MFP.
    + exact WF2.
    + exact CH2.
    + exact EE2.
    + exact NIF2.
    + apply (iftab_transport _ _ _ _ _ TAB3 MU5); [unfold FPRINTF_K; dj FAG MFP|].
      intros i n2 ix p Hi Hp.
      assert (Hi80 : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      pose proof TAB as (_ & TL & _).
      assert (Hp0 : u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
      { apply (u64_back _ _ _ _ _ Hp MUf3). dj FAG TL Hi80 EG. }
      destruct (TOK i n2 ix p Hi Hp0) as (T1 & _ & _ & T4 & _). unfold FPRINTF_K. dj T1 T4.
    + exact NX2.
    + exact SENT2.
    + exact NSENT2.
    + exact OPEN2.
    + exact MIS2.
    + exact OC2.
    + lia. }
Qed.

Lemma mk_pre_ext : forall sink, pre_ext (mk_pre sink).
Proof.
  intros sink r1 r2 m E H.
  unfold mk_pre, mark_errno_ok, mark_table_ok, mark_name_ok, mark_block_ok,
    frame_apart_gnl, apart_frame, arg, spZ, errno_at in *.
  repeat rewrite <- E. exact H.
Qed.

Lemma mk_wr_ext : forall sink, wr_ext (mk_wr sink).
Proof. intros sink r1 r2 m E. unfold mk_wr, arg, errno_at. repeat rewrite E. reflexivity. Qed.

Lemma mk_post_ext : forall sink, post_ext (mk_post sink).
Proof.
  intros sink r1 r2 m q1 q2 m' E1 E2 H. unfold mk_post, arg in *.
  repeat rewrite <- E1. repeat rewrite <- E2. exact H.
Qed.

(* the callees' contracts are hypotheses (released form) *)
Theorem reac_served_mark_holds :
  reac_link_alias_read_contract -> reac_served_decide_contract -> reac_link_alias_write_contract ->
  remember_contract -> reac_code_emit_contract -> fprintf_contract -> bcmp_contract ->
  reac_served_mark_contract.
Proof.
  intros HAR HDE HAW HRM HCE HFP HBC sink.
  change (leaf_fp REAC_SERVED_MARK 17248 (mk_pre sink) (mk_wr sink) (mk_post sink)).
  apply leaf_fp_intro.
  - exact (mk_pre_ext sink).
  - exact (mk_wr_ext sink).
  - exact (mk_post_ext sink).
  - exact (reac_served_mark_walk HAR HDE HAW HRM HCE HFP HBC sink).
Qed.

(* closed over the callees with a closed proof on the branch: reac_served_decide
   (lib/Prog/model_decide.v) and bcmp (lib/Prog/bcmp.v) *)
Theorem reac_served_mark_closed :
  reac_link_alias_read_contract -> reac_link_alias_write_contract ->
  remember_contract -> reac_code_emit_contract -> fprintf_contract -> reac_served_mark_contract.
Proof.
  intros HAR HAW HRM HCE HFP.
  exact (reac_served_mark_holds HAR model_decide.reac_served_decide_closed HAW HRM HCE HFP bcmp.bcmp_holds).
Qed.
