From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YP0b YM05 YG0d YB1v YI0w YI0z YI12 YC4a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YRo.
Import ListNotations.
Open Scope Z_scope.
Definition both3_xcalls : list (asym * Z) := [
(AS_check_table, AF_both3_check_table);
(AS_role_of, AF_both3_role_of);
(AS_check_sighting, AF_both3_check_sighting);
(AS_jtok_is, AF_both3_jtok_is);
(AS_json_scalar, AF_both3_json_scalar);
(AS_find_entry, AF_both3_find_entry);
(AS_reac_box_name, AF_both3_reac_box_name);
(AS_sb_dec, AF_both3_sb_dec);
(AS_sb_ch, AF_both3_sb_ch);
(AS_reac_disco_classify, AF_both3_reac_disco_classify);
(AS_classify_core, AF_both3_classify_core);
(AS_reac_disco_peer_lock_init, AF_both3_reac_disco_peer_lock_init);
(AS_reac_disco_classify_on_segment, AF_both3_reac_disco_classify_on_segment);
(AS_reac_disco_gate_init, AF_both3_reac_disco_gate_init);
(AS_reac_disco_gate_should_push, AF_both3_reac_disco_gate_should_push);
(AS_reac_disco_table_init, AF_both3_reac_disco_table_init);
(AS_reac_disco_table_observe, AF_both3_reac_disco_table_observe);
(AS_reac_disco_table_age, AF_both3_reac_disco_table_age);
(AS_reac_disco_table_json, AF_both3_reac_disco_table_json);
(AS_reac_ctrl_checksum_verify, AF_both3_reac_ctrl_checksum_verify);
(AS_reac_ctrl_parse, AF_both3_reac_ctrl_parse);
(AS_kind_of_link1, AF_both3_kind_of_link1);
(AS_reac_hunt_verdict_name, AF_both3_reac_hunt_verdict_name);
(AS_reac_hunt_init, AF_both3_reac_hunt_init);
(AS_reac_hunt_pin, AF_both3_reac_hunt_pin);
(AS_reac_hunt_silence_proven, AF_both3_reac_hunt_silence_proven);
(AS_reac_hunt_observe, AF_both3_reac_hunt_observe);
(AS_reac_hunt_step, AF_both3_reac_hunt_step);
(AS_reac_hunt_role, AF_both3_reac_hunt_role);
(AS_reac_hunt_heard_anything, AF_both3_reac_hunt_heard_anything);
(AS_reac_rate_snap, AF_both3_reac_rate_snap);
(AS_reac_frame_clean_len, AF_both3_reac_frame_clean_len);
(AS_reac_arbitrate, AF_both3_reac_arbitrate);
(AS_reac_rival_kind_of, AF_both3_reac_rival_kind_of);
(AS_reac_master_only_cadence_ns, AF_both3_reac_master_only_cadence_ns);
(AS_reac_sender_kind, AF_both3_reac_sender_kind);
(AS_reac_ports_parse, AF_both3_reac_ports_parse) ].
Definition PA_SF6_ENTRY : Z := tfib_sigma AS___asan_stack_free_6.
Definition tfib_in_seg (a : Z) (sg : Segment) : bool :=
(Z.of_N (seg_base sg) <=? a) && (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)).
Definition tfib_win (a : Z) : Z :=
match find (tfib_in_seg a) tfibsegs with
| Some sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) - a
| None => 0
end.
Lemma tfib_win_img : forall a k, 0 <= k < tfib_win a -> in_img tfibsegs (a + k).
Proof.
intros a k Hk. unfold tfib_win in Hk. destruct (find (tfib_in_seg a) tfibsegs) as [sg|] eqn:E; [|lia].
apply find_some in E. destruct E as [Hin Hb]. unfold tfib_in_seg in Hb.
apply andb_prop in Hb. destruct Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
exists sg. split; [exact Hin | lia].
Qed.
Definition tfib_glob_tails : list (Z * Z) := [(0x20f9e, 2); (0x20fe6, 2); (0x21005, 3); (0x21026, 2); (0x21045, 3); (0x21064, 4); (0x21085, 3); (0x210a6, 2); (0x210c6, 2); (0x210e6, 2); (0x21107, 1); (0x2112a, 6); (0x21145, 3); (0x21164, 4); (0x21187, 1); (0x211c7, 1); (0x211e7, 1); (0x21225, 3); (0x21243, 5); (0x21267, 1); (0x21286, 2); (0x212e4, 4); (0x21307, 1); (0x21342, 6); (0x21389, 7); (0x213c2, 6); (0x213e1, 7); (0x2140d, 3); (0x2142e, 2); (0x21451, 7); (0x21493, 5); (0x214cf, 1); (0x214ec, 4); (0x21505, 3); (0x21526, 2); (0x21562, 6); (0x215a7, 1); (0x215e7, 1); (0x21606, 2); (0x2168c, 4)].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Class PAXcalls (L : ptable asym) {PI : PAImg L} : Prop :=
pa_xcalls : forall s k, In (s, k) both3_xcalls -> pa_sigma s = pa_val A_TEXT + k.
Class PAObjImg (L : ptable asym) {PI : PAImg L} : Prop :=
pa_obj_img_all : forall i, (i < tfib_nobj)%nat -> YImgTop.IMG_LO <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= YImgTop.IMG_TOP.
Class PAHiImg (L : ptable asym) {PI : PAImg L} : Prop :=
pa_hi_img : forall j, (j < tfib_nhi)%nat -> 0 <= pa_val (A_HI j) /\ pa_val (A_HI j) < YImgTop.IMG_TOP.
Class PAObjVal (L : ptable asym) {PI : PAImg L} : Prop :=
pa_obj_val : forall i, (i < tfib_nobj)%nat -> pa_val (A_OBJ i) = tfib_obj i.
Class PARoPresent (L : ptable asym) {PI : PAImg L} : Prop :=
pa_ro_present : forall q sz x, In (q, sz) tfib_glob_tails -> q <= x < q + sz -> seg_rom pa_segs (Z_to_bv 64 x) <> None.
Class PAWinImg (L : ptable asym) {PI : PAImg L} : Prop := {
pa_obj_win : forall i off k, (i < tfib_nobj)%nat -> 0 <= k < tfib_win (tfib_obj i + off) -> in_img pa_segs (pa_val (A_OBJ i) + off + k);
pa_hi_win : forall j off k, (j < tfib_nhi)%nat -> 0 <= k < tfib_win (tfib_hi j + off) -> in_img pa_segs (pa_val (A_HI j) + off + k) }.
Section c.
Context {L : ptable asym} {PI : PAImg L} {PX : PAXcalls L}.
Lemma pa_sigma_check_table : pa_sigma AS_check_table = pa_val A_TEXT + AF_both3_check_table.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_role_of : pa_sigma AS_role_of = pa_val A_TEXT + AF_both3_role_of.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_sighting : pa_sigma AS_check_sighting = pa_val A_TEXT + AF_both3_check_sighting.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_jtok_is : pa_sigma AS_jtok_is = pa_val A_TEXT + AF_both3_jtok_is.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_json_scalar : pa_sigma AS_json_scalar = pa_val A_TEXT + AF_both3_json_scalar.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_find_entry : pa_sigma AS_find_entry = pa_val A_TEXT + AF_both3_find_entry.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_box_name : pa_sigma AS_reac_box_name = pa_val A_TEXT + AF_both3_reac_box_name.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_sb_dec : pa_sigma AS_sb_dec = pa_val A_TEXT + AF_both3_sb_dec.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_sb_ch : pa_sigma AS_sb_ch = pa_val A_TEXT + AF_both3_sb_ch.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_classify : pa_sigma AS_reac_disco_classify = pa_val A_TEXT + AF_both3_reac_disco_classify.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_classify_core : pa_sigma AS_classify_core = pa_val A_TEXT + AF_both3_classify_core.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_peer_lock_init : pa_sigma AS_reac_disco_peer_lock_init = pa_val A_TEXT + AF_both3_reac_disco_peer_lock_init.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_classify_on_segment : pa_sigma AS_reac_disco_classify_on_segment = pa_val A_TEXT + AF_both3_reac_disco_classify_on_segment.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_gate_init : pa_sigma AS_reac_disco_gate_init = pa_val A_TEXT + AF_both3_reac_disco_gate_init.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_gate_should_push : pa_sigma AS_reac_disco_gate_should_push = pa_val A_TEXT + AF_both3_reac_disco_gate_should_push.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_table_init : pa_sigma AS_reac_disco_table_init = pa_val A_TEXT + AF_both3_reac_disco_table_init.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_table_observe : pa_sigma AS_reac_disco_table_observe = pa_val A_TEXT + AF_both3_reac_disco_table_observe.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_table_age : pa_sigma AS_reac_disco_table_age = pa_val A_TEXT + AF_both3_reac_disco_table_age.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_table_json : pa_sigma AS_reac_disco_table_json = pa_val A_TEXT + AF_both3_reac_disco_table_json.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_checksum_verify : pa_sigma AS_reac_ctrl_checksum_verify = pa_val A_TEXT + AF_both3_reac_ctrl_checksum_verify.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_parse : pa_sigma AS_reac_ctrl_parse = pa_val A_TEXT + AF_both3_reac_ctrl_parse.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_kind_of_link1 : pa_sigma AS_kind_of_link1 = pa_val A_TEXT + AF_both3_kind_of_link1.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_verdict_name : pa_sigma AS_reac_hunt_verdict_name = pa_val A_TEXT + AF_both3_reac_hunt_verdict_name.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_init : pa_sigma AS_reac_hunt_init = pa_val A_TEXT + AF_both3_reac_hunt_init.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_pin : pa_sigma AS_reac_hunt_pin = pa_val A_TEXT + AF_both3_reac_hunt_pin.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_silence_proven : pa_sigma AS_reac_hunt_silence_proven = pa_val A_TEXT + AF_both3_reac_hunt_silence_proven.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_observe : pa_sigma AS_reac_hunt_observe = pa_val A_TEXT + AF_both3_reac_hunt_observe.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_step : pa_sigma AS_reac_hunt_step = pa_val A_TEXT + AF_both3_reac_hunt_step.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_role : pa_sigma AS_reac_hunt_role = pa_val A_TEXT + AF_both3_reac_hunt_role.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_heard_anything : pa_sigma AS_reac_hunt_heard_anything = pa_val A_TEXT + AF_both3_reac_hunt_heard_anything.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_rate_snap : pa_sigma AS_reac_rate_snap = pa_val A_TEXT + AF_both3_reac_rate_snap.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_frame_clean_len : pa_sigma AS_reac_frame_clean_len = pa_val A_TEXT + AF_both3_reac_frame_clean_len.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_arbitrate : pa_sigma AS_reac_arbitrate = pa_val A_TEXT + AF_both3_reac_arbitrate.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_rival_kind_of : pa_sigma AS_reac_rival_kind_of = pa_val A_TEXT + AF_both3_reac_rival_kind_of.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_master_only_cadence_ns : pa_sigma AS_reac_master_only_cadence_ns = pa_val A_TEXT + AF_both3_reac_master_only_cadence_ns.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_sender_kind : pa_sigma AS_reac_sender_kind = pa_val A_TEXT + AF_both3_reac_sender_kind.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ports_parse : pa_sigma AS_reac_ports_parse = pa_val A_TEXT + AF_both3_reac_ports_parse.
Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.
End c.
Section d.
Context {L : ptable asym} {PI : PAImg L} {POV : PAObjVal L}.
Lemma pa_obj_ro_unowned : forall B i, YRo.tfib_ro_unowned B -> In i [63; 64]%nat -> YRo.ro_unowned B (pa_val (A_OBJ i)) 8.
Proof.
intros B i H Hi. destruct Hi as [<-|[<-|[]]].
- rewrite (pa_obj_val 63%nat ltac:(unfold tfib_nobj; lia)). apply (YRo.tfib_ro_unowned_at B _ _ H).
  vm_compute. repeat (first [left; reflexivity | right]).
- rewrite (pa_obj_val 64%nat ltac:(unfold tfib_nobj; lia)). apply (YRo.tfib_ro_unowned_at B _ _ H).
  vm_compute. repeat (first [left; reflexivity | right]).
Qed.
End d.
End b.
