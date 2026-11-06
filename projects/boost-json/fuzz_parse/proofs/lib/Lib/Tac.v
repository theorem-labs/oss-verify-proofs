(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Export PropExec MState Mem Cells Exec Step Frame Arr Image.
From Ltac2 Require Ltac2.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc6option37Corelib4Init5Logicjd4True79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Tac~~~~~~l84ibndhc4prodjd3andl89opt_holds46Stdlib6ZArith6BinInt1Zr22lejd2eqr23addjd2orl84ib_Ll85ib_PQl84ib_Ul84ib_hl84ib_lhc4boolhc5falser23lebhc3orbhc4andbl87opt_gebl87opt_lebhc4truel87chk_litl85ib_okl86chk_sbhc4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hm2ddisjoint_fromhm23ivll88chks_litl86ibs_okl87chks_sbr23pow89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Tac8WithSegs~~~~~~hta9store_ctx04Npos35stdpp9bitvectorbdefinitionsij02bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~il38rw_cellsr26of_nathc6length3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsiqccwrite_to_mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~iv34celliv3acells_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jk52wail38ro_cellsjk58bytes_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~jpd5u8arrjpd6u32arrr23muljpd6u64arrjpd4u8rohm23stkhta8chk_hullhta9hull_factjd2exhm25munchhm25wmonohta8call_ctxhm26insidel89store_ctxl85wdescl84wd_hl85wd_hil84wd_ll85wd_lol8achk_insidel86wds_okhc3nativ38cells_wfl8bmk_CB_cellsl87sum_nativ3bcells_byteshc3apphc4cons3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypektd7Segmentiv32CB" s.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac is_concrete_map R ::=
  lazymatch R with
  | TNode _ _ _ => idtac
  | TEmpty => idtac
  | mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
  end.
Ltac map_cbv_get ::=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota delta [tget mkR] in g in set_concl g'.
Ltac map_cbv_set ::=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota delta [tset mkR] in g in set_concl g'.

(* [comment removed for export] *)
Ltac solve_load_image :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
      let E := addr_expr a in
      let Ez := zlit E in
      lazymatch goal with
      | HI : mem_inv segs m |- _ =>
          let obs := eval vm_compute in (image_bytes segs Ez n) in
          lazymatch obs with
          | Some ?bs =>
              let RO := fresh "ROimg" in
              assert (RO : ro_cells segs m Ez [CB n bs])
                by (apply (ro_cells_image segs m Ez bs HI); [vm_compute; reflexivity | lia | cbn; lia]);
              rewrite (ro_cells_read_at segs m Ez [CB n bs] 0%nat (CB n bs) n a RO)
                by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
              clear RO; load_post
          | None => fail "no readable image bytes at" Ez
          end
      end
  end.
Ltac solve_load ::= first [ solve_load_base | solve_load_image ].

(* [comment removed for export] *)
Ltac simpl_arr_sizes := rewrite ?u32s_length, ?u64s_length, ?upd_length in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfact : ltac2:(zQ "00>1PPP") := ltac2:(zQ "00\1PP^1").

Record ibnd := IB { ib_l : option Z; ib_h : option Z; ib_L : option Z; ib_U : option Z; ib_PQ : option (Z * Z) }.

Definition opt_holds : ltac2:(zQ "20!h9!j4>1o@1$1$0>1P>0$0PP") := ltac2:(zQ "30!h9!j4!l1\1o@1$1$0\1P>0$0PM1\1o@1$1$0P^2\1z$0@1^2^1$2").

Definition ib_ok : ltac2:(zQ "20!h9!p2>1X$0>2lo$0>2hi$0>1b$1P") := ltac2:(zQ "h00!h9!p9!q0!q6!sa!j4!sf!t4!l1!ta!tf!u6!ue!v5!vc!p2\1X$0\2lo$0\2hi$0\1b$f@2$2@2$3@1$e^1\1l$0@3$6$0^4@2$7^5^1@2$2@2$3@1$d^1\1h$0@3$6$0^3@2$7^5^1@2$2@2$3@1$a^1\1L$0@2$4^1^4@2$2@2$3@1$c^1\1U$0@2$4^3^1M5\1x@1$5@2$1$0$0P@1$b^1\1p@2$1$0$0M1\1p@2$1$0$0P^1\1P$0\1Q$0@2$9@2$4^5^2@2$4^1^6$8").

Definition opt_leb : ltac2:(zQ "30!h9!hg3!j4>1x$0>1o@1$2$0$1") := ltac2:(zQ "50!h9!j4!hg3!hga!hh2\1x$0\1o@1$1$0M1\1o@1$1$0$2^1\1z$0@2$4^3^1$3").
Definition opt_geb : ltac2:(zQ "30!h9!hg3!j4>1x$0>1o@1$2$0$1") := ltac2:(zQ "50!h9!j4!hg3!hga!hh2\1x$0\1o@1$1$0M1\1o@1$1$0$2^1\1z$0@2$4^1^3$3").

(* [comment removed for export] *)
Definition chk_lit : ltac2:(zQ "30!h9!hg3!p2>1b$2>1A$0>1s$0$1") := ltac2:(zQ "f0!h9!p9!hg3!j4!hh8!t4!hh2!hhe!hga!tf!u6!ue!p2!hi5!hif\1b$c\1A$0\1s$0@2$4@2$4@2$e@2$5^2^1@1$9^3@2$d^2@1$b^3M3\1x@1$3@2$1$0$0$2@1$a^3\1p@2$1$0$0M1\1p@2$1$0$0$2^1\1P$0\1Q$0@2$7@2$6^2^5@2$6@2$5^5^4^1$8").
(* [comment removed for export] *)
Definition chk_sb : ltac2:(zQ "30!h9!hg3!p2>1b$2>1c$0>1s$0$1") := ltac2:(zQ "80!h9!hh8!v5!vc!p2!hi5!hif!t4\1b$4\1c$0\1s$0@2$1@2$6@2$7^2^1@1$3^3@2$5^2@1$2^3").

Lemma chk_lit_sound : ltac2:(zQ "a0!h9!sa!hg3!hj9!sf!ta!hk0!hka!p2!t4>1X$0>2lo$0>2hi$0>1b$8>1A$0>1s$0>0@4$7^6^5^4^3>0@3$4$2@3$6^4^3^2$3@2$5@2$1@2$9^4^3^7@2$1^6^4").
Proof.
  intros X lo hi [l h L U PQ] A s (_ & _ & HL & HU & HPQ) Hc. unfold chk_lit in Hc. cbn in *.
  apply Bool.orb_true_iff in Hc. destruct Hc as [Hc|Hc]; [apply Bool.orb_true_iff in Hc; destruct Hc as [Hc|Hc]|].
  - destruct L as [L|]; cbn in *; [|discriminate]. apply Z.leb_le in Hc. lia.
  - destruct U as [U|]; cbn in *; [|discriminate]. apply Z.leb_le in Hc. lia.
  - destruct PQ as [[P Q]|]; [|discriminate]. apply Bool.andb_true_iff in Hc. destruct Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma chk_sb_sound : ltac2:(zQ "a0!h9!t4!sa!hg3!hj9!sf!ta!hl2!hka!p2>1X$0>2lo$0>2hi$0>1b$9>1c$0>1s$0>0@4$8^6^5^4^3>0@3$5$3@3$7^4^3^2$4@2$6@2$2@2$1@2$1^8^4^3^7@2$2^6@2$1^8^4").
Proof.
  intros X lo hi [l h L U PQ] c s (Hl & Hh & _ & _ & _) Hc. unfold chk_sb in Hc. cbn in *.
  apply Bool.orb_true_iff in Hc. destruct Hc as [Hc|Hc].
  - destruct l as [l|]; cbn in *; [|discriminate]. apply Z.leb_le in Hc. lia.
  - destruct h as [h|]; cbn in *; [|discriminate]. apply Z.leb_le in Hc. lia.
Qed.

Lemma chk_sb0_sound : ltac2:(zQ "a0!h9!sa!hg3!hj9!sf!ta!hl2!hka!p2!t4>1X$0>2lo$0>2hi$0>1b$8>1s$0>0@4$7^5^4^3^2>0@3$4$2@3$6^3Z^2$3@2$5@2$1@2$9^7^3^6@2$1^5^7").
Proof. intros X lo hi b s Hb Hc. pose proof (chk_sb_sound X lo hi b 0 s Hb Hc). lia. Qed.

(* [comment removed for export] *)
Fixpoint ibs_ok (X : Z) (W : list ivl) (B : list ibnd) : Prop :=
  match W, B with
  | [], [] => True
  | (lo, hi) :: W', b :: B' => ib_ok X lo hi b /\ ibs_ok X W' B'
  | _, _ => False
  end.

Fixpoint chks_lit (B : list ibnd) (A s : Z) : bool :=
  match B with [] => true | b :: B' => andb (chk_lit b A s) (chks_lit B' A s) end.
Fixpoint chks_sb (B : list ibnd) (c s : Z) : bool :=
  match B with [] => true | b :: B' => andb (chk_sb b c s) (chks_sb B' c s) end.

Lemma chks_lit_sound : ltac2:(zQ "a0!h9!hlb!hg3!hj9!sf!hpe!hqf!hr6!p2!hs1>1X$0>1W@1$1$6>1B@1$1$8>1A$0>1s$0>0@3$9^5^4^3>0@3$4$2@3$7^4^3^2$3@3$5^6^4^3").
Proof.
  intros X W. induction W as [|[lo hi] W IH]; intros [|b B] A s Hok Hc; cbn in *; try exact I; try contradiction.
  apply Bool.andb_true_iff in Hc. destruct Hc as [H1 H2]. destruct Hok as [Hb HB].
  split; [eapply chk_lit_sound; eauto | eapply IH; eauto].
Qed.

Lemma chks_sb_sound : ltac2:(zQ "b0!h9!hlb!hg3!hj9!sf!hpe!hqf!hsa!p2!hs1!t4>1X$0>1W@1$1$6>1B@1$1$8>1c$0>1s$0>0@3$9^5^4^3>0@3$4$2@3$7^4^3^2$3@3$5^6@2$a^7^4^3").
Proof.
  intros X W. induction W as [|[lo hi] W IH]; intros [|b B] c s Hok Hc; cbn in *; try exact I; try contradiction.
  apply Bool.andb_true_iff in Hc. destruct Hc as [H1 H2]. destruct Hok as [Hb HB].
  split; [eapply chk_sb_sound; eauto | eapply IH; eauto].
Qed.

Lemma chks_sb0_sound : ltac2:(zQ "a0!hlb!h9!hg3!hj9!sf!hpe!hqf!hsa!p2!hs1>1X$1>1W@1$0$6>1B@1$0$8>1s$1>0@3$9^4^3^2>0@3$4$2@3$7^3Z^2$3@3$5^5^6^3").
Proof. intros X W B s Hok Hc. pose proof (chks_sb_sound X W B 0 s Hok Hc) as D. rewrite Z.add_0_r in D. exact D. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithSegs.
Variable segs : ltac2:(zQ "20!hlb!lh2@1$0$1").

(* [comment removed for export] *)
Definition store_ctx : ltac2:(zQ "20!h9!p2>1a$0>1n$0>1X$0>1b$1P") := ltac2:(zQ "70!h9!q0!t4!sa!hka!p2!ht4\1a$0\1n$0\1X$0\1b$5@2$1@2$3Z^4@2$1@2$3@2$2^4^3@2$6+2+k0@4$4^2^4@2$2^4^3^1").

Lemma store_ctx_intro : ltac2:(zQ "70!h9!t4!sa!ihd!hka!p2!ht4>1a$0>1n$0>1X$0>1b$5>0@2$2Z^4>0@2$2@2$1^5^4@2$6+2+k0>0@4$4^4^6@2$1^6^5^3@4$3^7^6^5^4").
Proof. intros a n X b Ha Hl Hb. exact (conj Ha (conj Hl Hb)). Qed.

Lemma rw_cells_frame_lit : ltac2:(zQ "h20!iia!ikd!h9!hlb!ioe!ipa!hg3!iq3!j4!hj9!sf!iu3!jif!jj7!jnf!ihd!hk0!p2>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$2>2bs@1$3@1$1@1$0#8>1X$2>1b$h1>1A$2>2cs@1$3$c>0@4$f^6@1$5@2$7@1$1@1$0#8^5^4^3>0@4$4?4segs^8^3^2>0@3$a$6@3$h0^5^4@1$5@1$d^3$9@4$4?4segs@3$b^a@1$e^9^8^5^4").
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H Hc. apply rw_cells_frame; auto. eapply chk_lit_sound; eauto. Qed.

Lemma rw_cells_frame_sb : ltac2:(zQ "h30!iia!ikd!h9!hlb!ioe!t4!ipa!hg3!iq3!j4!hj9!sf!iu3!jif!jj7!jnf!ihd!hl2!p2>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$2>2bs@1$3@1$1@1$0#8>1X$2>1b$h2>1c$2>2cs@1$3$d>0@4$h0^6@1$6@2$8@1$1@1$0#8^5^4^3>0@4$4?4segs^8@2$5^5^3^2>0@3$b$7@3$h1^5^4@1$6@1$e^3$a@4$4?4segs@3$c^a@1$f^9^8@2$5^7^5^4").
Proof. intros m a bs X b c cs (Ha & Hl & Hb) H Hc. apply rw_cells_frame; auto. eapply chk_sb_sound; eauto. Qed.

Lemma rw_cells_frame_sb0 : ltac2:(zQ "h20!iia!ikd!hlb!h9!ioe!ipa!hg3!iq3!j4!hj9!sf!iu3!jif!jj7!jnf!ihd!hl2!p2>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$3>2bs@1$2@1$1@1$0#8>1X$3>1b$h1>2cs@1$2$c>0@4$f^5@1$5@2$7@1$1@1$0#8^4^3^2>0@4$4?4segs^7^4^2>0@3$a$6@3$h0^4Z@1$5@1$d^3$9@4$4?4segs@3$b^9@1$e^8^7^6^4").
Proof. intros m a bs X b cs (Ha & Hl & Hb) H Hc. apply rw_cells_frame; auto. eapply chk_sb0_sound; eauto. Qed.

(* [comment removed for export] *)
Lemma rw_cells_frame_h : ltac2:(zQ "h10!iia!ikd!h9!ipa!iq3!hlb!ioe!t4!sa!j4!ta!iu3!jif!jj7!jnf!ihd!p2>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$2>2bs@1$5@1$1@1$0#8>1X$2>1b$h0>1A$2>2cs@1$5$c>0@4$f^6@1$3@2$4@1$1@1$0#8^5^4^3>0@4$6?4segs^8^3^2>0@2$a@2$8@2$7^4@1$3@1$d^3^8@2$8@2$7^8@1$3@2$4@1$1@1$0#8^7^4@4$6?4segs@3$b^a@1$e^9^8^5^4").
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H Hd. apply rw_cells_frame; auto. Qed.

Lemma ro_cells_frame_lit : ltac2:(zQ "h20!iia!ikd!h9!hlb!jo5!ipa!hg3!iq3!j4!hj9!sf!iu3!jif!jj7!jnf!ihd!hk0!p2>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$2>2bs@1$3@1$1@1$0#8>1X$2>1b$h1>1A$2>2cs@1$3$c>0@4$f^6@1$5@2$7@1$1@1$0#8^5^4^3>0@4$4?4segs^8^3^2>0@3$a$6@3$h0^5^4@1$5@1$d^3$9@4$4?4segs@3$b^a@1$e^9^8^5^4").
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H Hc. apply ro_cells_frame; auto. eapply chk_lit_sound; eauto. Qed.
Lemma ro_cells_frame_sb : ltac2:(zQ "h30!iia!ikd!h9!hlb!jo5!t4!ipa!hg3!iq3!j4!hj9!sf!iu3!jif!jj7!jnf!ihd!hl2!p2>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$2>2bs@1$3@1$1@1$0#8>1X$2>1b$h2>1c$2>2cs@1$3$d>0@4$h0^6@1$6@2$8@1$1@1$0#8^5^4^3>0@4$4?4segs^8@2$5^5^3^2>0@3$b$7@3$h1^5^4@1$6@1$e^3$a@4$4?4segs@3$c^a@1$f^9^8@2$5^7^5^4").
Proof. intros m a bs X b c cs (Ha & Hl & Hb) H Hc. apply ro_cells_frame; auto. eapply chk_sb_sound; eauto. Qed.
Lemma ro_cells_frame_sb0 : ltac2:(zQ "h20!iia!ikd!hlb!h9!jo5!ipa!hg3!iq3!j4!hj9!sf!iu3!jif!jj7!jnf!ihd!hl2!p2>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$3>2bs@1$2@1$1@1$0#8>1X$3>1b$h1>2cs@1$2$c>0@4$f^5@1$5@2$7@1$1@1$0#8^4^3^2>0@4$4?4segs^7^4^2>0@3$a$6@3$h0^4Z@1$5@1$d^3$9@4$4?4segs@3$b^9@1$e^8^7^6^4").
Proof. intros m a bs X b cs (Ha & Hl & Hb) H Hc. apply ro_cells_frame; auto. eapply chk_sb0_sound; eauto. Qed.
Lemma ro_cells_frame_h : ltac2:(zQ "h10!iia!ikd!h9!ipa!iq3!hlb!jo5!t4!sa!j4!ta!iu3!jif!jj7!jnf!ihd!p2>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$2>2bs@1$5@1$1@1$0#8>1X$2>1b$h0>1A$2>2cs@1$5$c>0@4$f^6@1$3@2$4@1$1@1$0#8^5^4^3>0@4$6?4segs^8^3^2>0@2$a@2$8@2$7^4@1$3@1$d^3^8@2$8@2$7^8@1$3@2$4@1$1@1$0#8^7^4@4$6?4segs@3$b^a@1$e^9^8^5^4").
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H Hd. apply ro_cells_frame; auto. Qed.

Lemma bytes_at_write_other_lit : ltac2:(zQ "h00!iia!ikd!h9!iq3!hlb!jp1!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hk0!p2>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$2>2bs@1$4@1$1@1$0#8>1X$2>1b$f>1A$2>2cs@1$4@1$1@1$0#8>0@4$d^6@1$6@2$3@1$1@1$0#8^5^4^3>0@4$5?4segs^8^3^2>0@3$a$7@3$e^5^4@1$6@2$3@1$1@1$0#8^3$9@4$5?4segs@3$b^a@1$c^9^8^5^4").
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H Hc. apply bytes_at_write_other; auto. eapply chk_lit_sound; eauto. Qed.
Lemma bytes_at_write_other_sb : ltac2:(zQ "h10!iia!ikd!h9!iq3!hlb!jp1!t4!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hl2!p2>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$2>2bs@1$4@1$1@1$0#8>1X$2>1b$h0>1c$2>2cs@1$4@1$1@1$0#8>0@4$e^6@1$7@2$3@1$1@1$0#8^5^4^3>0@4$5?4segs^8@2$6^5^3^2>0@3$b$8@3$f^5^4@1$7@2$3@1$1@1$0#8^3$a@4$5?4segs@3$c^a@1$d^9^8@2$6^7^5^4").
Proof. intros m a bs X b c cs (Ha & Hl & Hb) H Hc. apply bytes_at_write_other; auto. eapply chk_sb_sound; eauto. Qed.
Lemma bytes_at_write_other_sb0 : ltac2:(zQ "h00!iia!ikd!iq3!hlb!h9!jp1!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hl2!p2>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$4>2bs@1$3@1$1@1$0#8>1X$4>1b$f>2cs@1$3@1$1@1$0#8>0@4$d^5@1$6@2$2@1$1@1$0#8^4^3^2>0@4$5?4segs^7^4^2>0@3$a$7@3$e^4Z@1$6@2$2@1$1@1$0#8^3$9@4$5?4segs@3$b^9@1$c^8^7^6^4").
Proof. intros m a bs X b cs (Ha & Hl & Hb) H Hc. apply bytes_at_write_other; auto. eapply chk_sb0_sound; eauto. Qed.
Lemma bytes_at_write_other_h : ltac2:(zQ "f0!iia!ikd!iq3!h9!ipa!hlb!jp1!t4!sa!j4!ta!iu3!jnf!ihd!p2>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$3>2bs@1$5@1$1@1$0#8>1X$3>1b$e>1A$3>2cs@1$5@1$1@1$0#8>0@4$d^6@1$4@2$2@1$1@1$0#8^5^4^3>0@4$6?4segs^8^3^2>0@2$a@2$8@2$7^4@1$4@2$2@1$1@1$0#8^3^8@2$8@2$7^8@1$4@2$2@1$1@1$0#8^7^4@4$6?4segs@3$b^a@1$c^9^8^5^4").
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H Hd. apply bytes_at_write_other; auto. Qed.

Lemma u8arr_frame_lit : ltac2:(zQ "h00!iia!ikd!h9!iq3!hlb!jt7!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hk0!p2>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$2>2bs@1$4@1$1@1$0#8>1X$2>1b$f>1A$2>2xs@1$4@1$1@1$0#8>0@4$d^6@1$6@2$3@1$1@1$0#8^5^4^3>0@4$5?4segs^8^3^2>0@3$a$7@3$e^5^4@1$6@2$3@1$1@1$0#8^3$9@4$5?4segs@3$b^a@1$c^9^8^5^4").
Proof. intros m a bs X b A xs (Ha & Hl & Hb) H Hc. apply u8arr_frame; auto. eapply chk_lit_sound; eauto. Qed.
Lemma u8arr_frame_sb : ltac2:(zQ "h10!iia!ikd!h9!iq3!hlb!jt7!t4!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hl2!p2>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$2>2bs@1$4@1$1@1$0#8>1X$2>1b$h0>1c$2>2xs@1$4@1$1@1$0#8>0@4$e^6@1$7@2$3@1$1@1$0#8^5^4^3>0@4$5?4segs^8@2$6^5^3^2>0@3$b$8@3$f^5^4@1$7@2$3@1$1@1$0#8^3$a@4$5?4segs@3$c^a@1$d^9^8@2$6^7^5^4").
Proof. intros m a bs X b c xs (Ha & Hl & Hb) H Hc. apply u8arr_frame; auto. eapply chk_sb_sound; eauto. Qed.
Lemma u8arr_frame_sb0 : ltac2:(zQ "h00!iia!ikd!iq3!hlb!h9!jt7!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hl2!p2>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$4>2bs@1$3@1$1@1$0#8>1X$4>1b$f>2xs@1$3@1$1@1$0#8>0@4$d^5@1$6@2$2@1$1@1$0#8^4^3^2>0@4$5?4segs^7^4^2>0@3$a$7@3$e^4Z@1$6@2$2@1$1@1$0#8^3$9@4$5?4segs@3$b^9@1$c^8^7^6^4").
Proof. intros m a bs X b xs (Ha & Hl & Hb) H Hc. apply u8arr_frame; auto. eapply chk_sb0_sound; eauto. Qed.
Lemma u8arr_frame_h : ltac2:(zQ "f0!iia!ikd!iq3!h9!ipa!hlb!jt7!t4!sa!j4!ta!iu3!jnf!ihd!p2>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$3>2bs@1$5@1$1@1$0#8>1X$3>1b$e>1A$3>2xs@1$5@1$1@1$0#8>0@4$d^6@1$4@2$2@1$1@1$0#8^5^4^3>0@4$6?4segs^8^3^2>0@2$a@2$8@2$7^4@1$4@2$2@1$1@1$0#8^3^8@2$8@2$7^8@1$4@2$2@1$1@1$0#8^7^4@4$6?4segs@3$b^a@1$c^9^8^5^4").
Proof. intros m a bs X b A xs (Ha & Hl & Hb) H Hd. apply u8arr_frame; auto. Qed.

Lemma u32arr_frame_lit : ltac2:(zQ "h10!iia!ikd!h9!iq3!hlb!ju0!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hk0!p2!jua>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$2>2bs@1$4@1$1@1$0#8>1X$2>1b$f>1A$2>2ws@1$4@1$1@1$0#k0>0@4$d^6@1$6@2$3@1$1@1$0#8^5^4^3>0@4$5?4segs^8^3^2>0@3$a$7@3$e^5^4@2$h0+4@1$6@2$3@1$1@1$0#k0^3$9@4$5?4segs@3$b^a@1$c^9^8^5^4").
Proof. intros m a bs X b A ws (Ha & Hl & Hb) H Hc. apply u32arr_frame; auto. eapply chk_lit_sound; eauto. Qed.
Lemma u32arr_frame_sb : ltac2:(zQ "h20!iia!ikd!h9!iq3!hlb!ju0!t4!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hl2!p2!jua>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$2>2bs@1$4@1$1@1$0#8>1X$2>1b$h0>1c$2>2ws@1$4@1$1@1$0#k0>0@4$e^6@1$7@2$3@1$1@1$0#8^5^4^3>0@4$5?4segs^8@2$6^5^3^2>0@3$b$8@3$f^5^4@2$h1+4@1$7@2$3@1$1@1$0#k0^3$a@4$5?4segs@3$c^a@1$d^9^8@2$6^7^5^4").
Proof. intros m a bs X b c ws (Ha & Hl & Hb) H Hc. apply u32arr_frame; auto. eapply chk_sb_sound; eauto. Qed.
Lemma u32arr_frame_sb0 : ltac2:(zQ "h10!iia!ikd!iq3!hlb!h9!ju0!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hl2!p2!jua>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$4>2bs@1$3@1$1@1$0#8>1X$4>1b$f>2ws@1$3@1$1@1$0#k0>0@4$d^5@1$6@2$2@1$1@1$0#8^4^3^2>0@4$5?4segs^7^4^2>0@3$a$7@3$e^4Z@2$h0+4@1$6@2$2@1$1@1$0#k0^3$9@4$5?4segs@3$b^9@1$c^8^7^6^4").
Proof. intros m a bs X b ws (Ha & Hl & Hb) H Hc. apply u32arr_frame; auto. eapply chk_sb0_sound; eauto. Qed.
Lemma u32arr_frame_h : ltac2:(zQ "h00!iia!ikd!iq3!h9!ipa!hlb!ju0!t4!sa!j4!ta!iu3!jnf!ihd!p2!jua>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$3>2bs@1$5@1$1@1$0#8>1X$3>1b$e>1A$3>2ws@1$5@1$1@1$0#k0>0@4$d^6@1$4@2$2@1$1@1$0#8^5^4^3>0@4$6?4segs^8^3^2>0@2$a@2$8@2$7^4@2$f+4@1$4@2$2@1$1@1$0#k0^3^8@2$8@2$7^8@1$4@2$2@1$1@1$0#8^7^4@4$6?4segs@3$b^a@1$c^9^8^5^4").
Proof. intros m a bs X b A ws (Ha & Hl & Hb) H Hd. apply u32arr_frame; auto. Qed.

Lemma u64arr_frame_lit : ltac2:(zQ "h10!iia!ikd!h9!iq3!hlb!jv0!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hk0!p2!jua>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$2>2bs@1$4@1$1@1$0#8>1X$2>1b$f>1A$2>2ws@1$4@1$1@1$0#k0>0@4$d^6@1$6@2$3@1$1@1$0#8^5^4^3>0@4$5?4segs^8^3^2>0@3$a$7@3$e^5^4@2$h0+8@1$6@2$3@1$1@1$0#k0^3$9@4$5?4segs@3$b^a@1$c^9^8^5^4").
Proof. intros m a bs X b A ws (Ha & Hl & Hb) H Hc. apply u64arr_frame; auto. eapply chk_lit_sound; eauto. Qed.
Lemma u64arr_frame_sb : ltac2:(zQ "h20!iia!ikd!h9!iq3!hlb!jv0!t4!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hl2!p2!jua>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$2>2bs@1$4@1$1@1$0#8>1X$2>1b$h0>1c$2>2ws@1$4@1$1@1$0#k0>0@4$e^6@1$7@2$3@1$1@1$0#8^5^4^3>0@4$5?4segs^8@2$6^5^3^2>0@3$b$8@3$f^5^4@2$h1+8@1$7@2$3@1$1@1$0#k0^3$a@4$5?4segs@3$c^a@1$d^9^8@2$6^7^5^4").
Proof. intros m a bs X b c ws (Ha & Hl & Hb) H Hc. apply u64arr_frame; auto. eapply chk_sb_sound; eauto. Qed.
Lemma u64arr_frame_sb0 : ltac2:(zQ "h10!iia!ikd!iq3!hlb!h9!jv0!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hl2!p2!jua>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$4>2bs@1$3@1$1@1$0#8>1X$4>1b$f>2ws@1$3@1$1@1$0#k0>0@4$d^5@1$6@2$2@1$1@1$0#8^4^3^2>0@4$5?4segs^7^4^2>0@3$a$7@3$e^4Z@2$h0+8@1$6@2$2@1$1@1$0#k0^3$9@4$5?4segs@3$b^9@1$c^8^7^6^4").
Proof. intros m a bs X b ws (Ha & Hl & Hb) H Hc. apply u64arr_frame; auto. eapply chk_sb0_sound; eauto. Qed.
Lemma u64arr_frame_h : ltac2:(zQ "h00!iia!ikd!iq3!h9!ipa!hlb!jv0!t4!sa!j4!ta!iu3!jnf!ihd!p2!jua>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$3>2bs@1$5@1$1@1$0#8>1X$3>1b$e>1A$3>2ws@1$5@1$1@1$0#k0>0@4$d^6@1$4@2$2@1$1@1$0#8^5^4^3>0@4$6?4segs^8^3^2>0@2$a@2$8@2$7^4@2$f+8@1$4@2$2@1$1@1$0#k0^3^8@2$8@2$7^8@1$4@2$2@1$1@1$0#8^7^4@4$6?4segs@3$b^a@1$c^9^8^5^4").
Proof. intros m a bs X b A ws (Ha & Hl & Hb) H Hd. apply u64arr_frame; auto. Qed.

Lemma u8ro_frame_lit : ltac2:(zQ "h00!iia!ikd!h9!iq3!hlb!jva!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hk0!p2>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$2>2bs@1$4@1$1@1$0#8>1X$2>1b$f>1A$2>2xs@1$4@1$1@1$0#8>0@4$d^6@1$6@2$3@1$1@1$0#8^5^4^3>0@4$5?4segs^8^3^2>0@3$a$7@3$e^5^4@1$6@2$3@1$1@1$0#8^3$9@4$5?4segs@3$b^a@1$c^9^8^5^4").
Proof. intros m a bs X b A xs (Ha & Hl & Hb) H Hc. apply u8ro_frame; auto. eapply chk_lit_sound; eauto. Qed.
Lemma u8ro_frame_sb : ltac2:(zQ "h10!iia!ikd!h9!iq3!hlb!jva!t4!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hl2!p2>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$2>2bs@1$4@1$1@1$0#8>1X$2>1b$h0>1c$2>2xs@1$4@1$1@1$0#8>0@4$e^6@1$7@2$3@1$1@1$0#8^5^4^3>0@4$5?4segs^8@2$6^5^3^2>0@3$b$8@3$f^5^4@1$7@2$3@1$1@1$0#8^3$a@4$5?4segs@3$c^a@1$d^9^8@2$6^7^5^4").
Proof. intros m a bs X b c xs (Ha & Hl & Hb) H Hc. apply u8ro_frame; auto. eapply chk_sb_sound; eauto. Qed.
Lemma u8ro_frame_sb0 : ltac2:(zQ "h00!iia!ikd!iq3!hlb!h9!jva!ipa!hg3!j4!hj9!sf!iu3!jnf!ihd!hl2!p2>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$4>2bs@1$3@1$1@1$0#8>1X$4>1b$f>2xs@1$3@1$1@1$0#8>0@4$d^5@1$6@2$2@1$1@1$0#8^4^3^2>0@4$5?4segs^7^4^2>0@3$a$7@3$e^4Z@1$6@2$2@1$1@1$0#8^3$9@4$5?4segs@3$b^9@1$c^8^7^6^4").
Proof. intros m a bs X b xs (Ha & Hl & Hb) H Hc. apply u8ro_frame; auto. eapply chk_sb0_sound; eauto. Qed.
Lemma u8ro_frame_h : ltac2:(zQ "f0!iia!ikd!iq3!h9!ipa!hlb!jva!t4!sa!j4!ta!iu3!jnf!ihd!p2>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1a$3>2bs@1$5@1$1@1$0#8>1X$3>1b$e>1A$3>2xs@1$5@1$1@1$0#8>0@4$d^6@1$4@2$2@1$1@1$0#8^5^4^3>0@4$6?4segs^8^3^2>0@2$a@2$8@2$7^4@1$4@2$2@1$1@1$0#8^3^8@2$8@2$7^8@1$4@2$2@1$1@1$0#8^7^4@4$6?4segs@3$b^a@1$c^9^8^5^4").
Proof. intros m a bs X b A xs (Ha & Hl & Hb) H Hd. apply u8ro_frame; auto. Qed.

Lemma stk_write_h : ltac2:(zQ "c0!iia!h9!ikd!kg2!iq3!hlb!j4!iu3!jnf!ihd!p2!ipa>1m>0@1$2@1$0#k0@1$6@1$2@1$0#8>2lo$1>2hi$1>1a$1>2bs@1$5@1$2@1$0#8>1X$1>1b$a>0@4$9^4@1$b@2$4@1$2@1$0#8^3^2^1>0@4$3?4segs^8^7^6@4$3?4segs@3$7^9@1$8^6^5^8^7").
Proof. intros m lo hi a bs X b (Ha & Hl & Hb) H. apply stk_write; auto. Qed.

(* [comment removed for export] *)
Definition hull_fact : ltac2:(zQ "10!h9>1a$0>1n$0>1P$0>1Q$0P") := ltac2:(zQ "40!h9!sa!ta!t4\1a$0\1n$0\1P$0\1Q$0@2$2@2$1@2$3^4^3^2@2$1^1^4").
Definition hull_none : ltac2:(zQ "10!h9>1a$0>1n$0P") := ltac2:(zQ "20!h9!l1\1a$0\1n$0$1").
Definition chk_hull : ltac2:(zQ "20!h9!hg3>1P$0>1Q$0>1A$0>1s$0$1") := ltac2:(zQ "40!h9!hh2!hhe!t4\1P$0\1Q$0\1A$0\1s$0@2$2@2$1^4^2@2$1@2$3^2^1^3").
Lemma chk_hull_sound : ltac2:(zQ "90!h9!t4!sa!hg3!hj9!sf!ta!kg9!kh5>1a$0>1n$0>1P$0>1Q$0>1A$0>1s$0>0@4$8^6^5^4^3>0@3$5$3@4$7^5^4^3^2$4@2$6@2$2@2$1^4^3^8@2$2@2$1^8^7^4").
Proof.
  intros a n P Q A s HF Hc. unfold hull_fact in HF. unfold chk_hull in Hc.
  apply Bool.andb_true_iff in Hc. destruct Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma rw_cells_frame_hl : ltac2:(zQ "h30!iia!h9!ikd!ipa!iq3!hlb!ioe!hg3!j4!hj9!sf!iu3!jif!jj7!jnf!kg9!kh5!ihd!p2>1m>0@1$2@1$0#k0@1$8@1$2@1$0#8>1a$1>2bs@1$5@1$2@1$0#8>1X$1>1b$h2>1A$1>2cs@1$5$c>0@4$h1^6@1$3@2$4@1$2@1$0#8^5^4^3>0@4$6?4segs^8^3^2>1P$1>1Q$1>0@4$h0^a@1$3@2$4@1$2@1$0#8^9^2^1>0@3$a$7@4$f^3^2^7@1$3@1$d^6$9@4$6?4segs@3$b^d@1$e^c^b^8^7").
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H P Q HF Hc. apply rw_cells_frame; auto. eapply chk_hull_sound; eauto. Qed.
Lemma ro_cells_frame_hl : ltac2:(zQ "h30!iia!h9!ikd!ipa!iq3!hlb!jo5!hg3!j4!hj9!sf!iu3!jif!jj7!jnf!kg9!kh5!ihd!p2>1m>0@1$2@1$0#k0@1$8@1$2@1$0#8>1a$1>2bs@1$5@1$2@1$0#8>1X$1>1b$h2>1A$1>2cs@1$5$c>0@4$h1^6@1$3@2$4@1$2@1$0#8^5^4^3>0@4$6?4segs^8^3^2>1P$1>1Q$1>0@4$h0^a@1$3@2$4@1$2@1$0#8^9^2^1>0@3$a$7@4$f^3^2^7@1$3@1$d^6$9@4$6?4segs@3$b^d@1$e^c^b^8^7").
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H P Q HF Hc. apply ro_cells_frame; auto. eapply chk_hull_sound; eauto. Qed.
Lemma bytes_at_write_other_hl : ltac2:(zQ "h10!iia!ikd!h9!iq3!ipa!hlb!jp1!hg3!j4!hj9!sf!iu3!jnf!kg9!kh5!ihd!p2>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$2>2bs@1$5@1$1@1$0#8>1X$2>1b$h0>1A$2>2cs@1$5@1$1@1$0#8>0@4$f^6@1$4@2$3@1$1@1$0#8^5^4^3>0@4$6?4segs^8^3^2>1P$2>1Q$2>0@4$e^a@1$4@2$3@1$1@1$0#8^9^2^1>0@3$a$7@4$d^3^2^7@1$4@2$3@1$1@1$0#8^6$9@4$6?4segs@3$b^d@1$c^c^b^8^7").
Proof. intros m a bs X b A cs (Ha & Hl & Hb) H P Q HF Hc. apply bytes_at_write_other; auto. eapply chk_hull_sound; eauto. Qed.
Lemma u8arr_frame_hl : ltac2:(zQ "h10!iia!ikd!h9!iq3!ipa!hlb!jt7!hg3!j4!hj9!sf!iu3!jnf!kg9!kh5!ihd!p2>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$2>2bs@1$5@1$1@1$0#8>1X$2>1b$h0>1A$2>2xs@1$5@1$1@1$0#8>0@4$f^6@1$4@2$3@1$1@1$0#8^5^4^3>0@4$6?4segs^8^3^2>1P$2>1Q$2>0@4$e^a@1$4@2$3@1$1@1$0#8^9^2^1>0@3$a$7@4$d^3^2^7@1$4@2$3@1$1@1$0#8^6$9@4$6?4segs@3$b^d@1$c^c^b^8^7").
Proof. intros m a bs X b A xs (Ha & Hl & Hb) H P Q HF Hc. apply u8arr_frame; auto. eapply chk_hull_sound; eauto. Qed.
Lemma u32arr_frame_hl : ltac2:(zQ "h20!iia!ikd!h9!iq3!ipa!hlb!ju0!hg3!j4!hj9!sf!iu3!jnf!kg9!kh5!ihd!p2!jua>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$2>2bs@1$5@1$1@1$0#8>1X$2>1b$h0>1A$2>2ws@1$5@1$1@1$0#k0>0@4$f^6@1$4@2$3@1$1@1$0#8^5^4^3>0@4$6?4segs^8^3^2>1P$2>1Q$2>0@4$e^a@1$4@2$3@1$1@1$0#8^9^2^1>0@3$a$7@4$d^3^2^7@2$h1+4@1$4@2$3@1$1@1$0#k0^6$9@4$6?4segs@3$b^d@1$c^c^b^8^7").
Proof. intros m a bs X b A ws (Ha & Hl & Hb) H P Q HF Hc. apply u32arr_frame; auto. eapply chk_hull_sound; eauto. Qed.
Lemma u64arr_frame_hl : ltac2:(zQ "h20!iia!ikd!h9!iq3!ipa!hlb!jv0!hg3!j4!hj9!sf!iu3!jnf!kg9!kh5!ihd!p2!jua>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$2>2bs@1$5@1$1@1$0#8>1X$2>1b$h0>1A$2>2ws@1$5@1$1@1$0#k0>0@4$f^6@1$4@2$3@1$1@1$0#8^5^4^3>0@4$6?4segs^8^3^2>1P$2>1Q$2>0@4$e^a@1$4@2$3@1$1@1$0#8^9^2^1>0@3$a$7@4$d^3^2^7@2$h1+8@1$4@2$3@1$1@1$0#k0^6$9@4$6?4segs@3$b^d@1$c^c^b^8^7").
Proof. intros m a bs X b A ws (Ha & Hl & Hb) H P Q HF Hc. apply u64arr_frame; auto. eapply chk_hull_sound; eauto. Qed.
Lemma u8ro_frame_hl : ltac2:(zQ "h10!iia!ikd!h9!iq3!ipa!hlb!jva!hg3!j4!hj9!sf!iu3!jnf!kg9!kh5!ihd!p2>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a$2>2bs@1$5@1$1@1$0#8>1X$2>1b$h0>1A$2>2xs@1$5@1$1@1$0#8>0@4$f^6@1$4@2$3@1$1@1$0#8^5^4^3>0@4$6?4segs^8^3^2>1P$2>1Q$2>0@4$e^a@1$4@2$3@1$1@1$0#8^9^2^1>0@3$a$7@4$d^3^2^7@1$4@2$3@1$1@1$0#8^6$9@4$6?4segs@3$b^d@1$c^c^b^8^7").
Proof. intros m a bs X b A xs (Ha & Hl & Hb) H P Q HF Hc. apply u8ro_frame; auto. eapply chk_hull_sound; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition call_ctx : ltac2:(zQ "61!iia!ikd!j4!hlb!h9!p2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$3$5P") := ltac2:(zQ "c1!iia!ikd!hlb!j4!q0!hqf!ki2!h9!ki7!kj0!p2!hs1&>0@1$1@1$0#k0@1$3@1$1@1$0#8\1m~0\2m'~0\1X$7\1B@1$2$a@2$6@1$2$5\1W@1$2$5@2$4@3$8^1^5^4@2$4@3$9?4segs^5^4@3$b^3^1^2").

Lemma call_ctx_intro : ltac2:(zQ "b1!iia!ikd!hlb!j4!h9!hqf!ki7!kj0!kj9!p2!hs1&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1W@1$2$5>1m~0>2m'~0>1X$4>1B@1$2$9>0@3$6^5^4^3>0@3$7?4segs^5^4>0@3$a^4^7^3@4$8^7^6^5^4").
Proof. intros W m m0 X B MU WM HB. exists W. exact (conj MU (conj WM HB)). Qed.

Lemma bytes_at_transport_lit : ltac2:(zQ "e1!iia!ikd!hlb!j4!h9!jp1!hg3!iq3!hj9!sf!kj9!hr6!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$c>1A$4>2bs@1$2@1$1@1$0#8>0@4$a^6^5^4^3>0@4$5?4segs^7^3^2>0@3$9$6@3$b^5^4@1$d@2$7@1$1@1$0#8^3$8@4$5?4segs^8^5^4").
Proof. intros m m' X B A bs (W & MU & WM & HB) H Hc. eapply bytes_at_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma bytes_at_transport_sb : ltac2:(zQ "f1!iia!ikd!hlb!j4!h9!jp1!t4!hg3!iq3!hj9!sf!kj9!hsa!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$d>1c$4>2bs@1$2@1$1@1$0#8>0@4$b^6^5^4^3>0@4$5?4segs^7@2$6^5^3^2>0@3$a$7@3$c^5^4@1$e@2$8@1$1@1$0#8^3$9@4$5?4segs^8@2$6^7^5^4").
Proof. intros m m' X B c bs (W & MU & WM & HB) H Hc. eapply bytes_at_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma bytes_at_transport_sb0 : ltac2:(zQ "e1!iia!ikd!hlb!j4!jp1!hg3!iq3!hj9!sf!h9!kj9!hsa!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$9>1B@1$2$c>2bs@1$2@1$1@1$0#8>0@4$a^5^4^3^2>0@4$4?4segs^6^4^2>0@3$8$5@3$b^4Z@1$d@2$6@1$1@1$0#8^3$7@4$4?4segs^7^6^4").
Proof. intros m m' X B bs (W & MU & WM & HB) H Hc. eapply bytes_at_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

Lemma rw_cells_transport_lit : ltac2:(zQ "f1!iia!ikd!hlb!j4!h9!ioe!hg3!hj9!sf!jif!jj7!kj9!hr6!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$d>1A$4>2cs@1$2$9>0@4$b^6^5^4^3>0@4$5?4segs^7^3^2>0@3$8$6@3$c^5^4@1$e@1$a^3$7@4$5?4segs^8^5^4").
Proof. intros m m' X B A cs (W & MU & WM & HB) H Hc. eapply rw_cells_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma rw_cells_transport_sb : ltac2:(zQ "h01!iia!ikd!hlb!j4!h9!ioe!t4!hg3!hj9!sf!jif!jj7!kj9!hsa!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$e>1c$4>2cs@1$2$a>0@4$c^6^5^4^3>0@4$5?4segs^7@2$6^5^3^2>0@3$9$7@3$d^5^4@1$f@1$b^3$8@4$5?4segs^8@2$6^7^5^4").
Proof. intros m m' X B c cs (W & MU & WM & HB) H Hc. eapply rw_cells_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma rw_cells_transport_sb0 : ltac2:(zQ "f1!iia!ikd!hlb!j4!ioe!hg3!hj9!sf!h9!jif!jj7!kj9!hsa!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$8>1B@1$2$d>2cs@1$2$9>0@4$b^5^4^3^2>0@4$4?4segs^6^4^2>0@3$7$5@3$c^4Z@1$e@1$a^3$6@4$4?4segs^7^6^4").
Proof. intros m m' X B cs (W & MU & WM & HB) H Hc. eapply rw_cells_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

Lemma ro_cells_transport_lit : ltac2:(zQ "f1!iia!ikd!hlb!j4!h9!jo5!hg3!hj9!sf!jif!jj7!kj9!hr6!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$d>1A$4>2cs@1$2$9>0@4$b^6^5^4^3>0@4$5?4segs^7^3^2>0@3$8$6@3$c^5^4@1$e@1$a^3$7@4$5?4segs^8^5^4").
Proof. intros m m' X B A cs (W & MU & WM & HB) H Hc. eapply ro_cells_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma ro_cells_transport_sb : ltac2:(zQ "h01!iia!ikd!hlb!j4!h9!jo5!t4!hg3!hj9!sf!jif!jj7!kj9!hsa!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$e>1c$4>2cs@1$2$a>0@4$c^6^5^4^3>0@4$5?4segs^7@2$6^5^3^2>0@3$9$7@3$d^5^4@1$f@1$b^3$8@4$5?4segs^8@2$6^7^5^4").
Proof. intros m m' X B c cs (W & MU & WM & HB) H Hc. eapply ro_cells_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma ro_cells_transport_sb0 : ltac2:(zQ "f1!iia!ikd!hlb!j4!jo5!hg3!hj9!sf!h9!jif!jj7!kj9!hsa!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$8>1B@1$2$d>2cs@1$2$9>0@4$b^5^4^3^2>0@4$4?4segs^6^4^2>0@3$7$5@3$c^4Z@1$e@1$a^3$6@4$4?4segs^7^6^4").
Proof. intros m m' X B cs (W & MU & WM & HB) H Hc. eapply ro_cells_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

Lemma u8arr_transport_lit : ltac2:(zQ "e1!iia!ikd!hlb!j4!h9!jt7!hg3!iq3!hj9!sf!kj9!hr6!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$c>1A$4>2xs@1$2@1$1@1$0#8>0@4$a^6^5^4^3>0@4$5?4segs^7^3^2>0@3$9$6@3$b^5^4@1$d@2$7@1$1@1$0#8^3$8@4$5?4segs^8^5^4").
Proof. intros m m' X B A xs (W & MU & WM & HB) H Hc. eapply u8arr_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma u8arr_transport_sb : ltac2:(zQ "f1!iia!ikd!hlb!j4!h9!jt7!t4!hg3!iq3!hj9!sf!kj9!hsa!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$d>1c$4>2xs@1$2@1$1@1$0#8>0@4$b^6^5^4^3>0@4$5?4segs^7@2$6^5^3^2>0@3$a$7@3$c^5^4@1$e@2$8@1$1@1$0#8^3$9@4$5?4segs^8@2$6^7^5^4").
Proof. intros m m' X B c xs (W & MU & WM & HB) H Hc. eapply u8arr_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma u8arr_transport_sb0 : ltac2:(zQ "e1!iia!ikd!hlb!j4!jt7!hg3!iq3!hj9!sf!h9!kj9!hsa!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$9>1B@1$2$c>2xs@1$2@1$1@1$0#8>0@4$a^5^4^3^2>0@4$4?4segs^6^4^2>0@3$8$5@3$b^4Z@1$d@2$6@1$1@1$0#8^3$7@4$4?4segs^7^6^4").
Proof. intros m m' X B xs (W & MU & WM & HB) H Hc. eapply u8arr_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

Lemma u32arr_transport_lit : ltac2:(zQ "f1!iia!ikd!hlb!j4!h9!ju0!hg3!iq3!hj9!sf!kj9!hr6!p2!jua!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$c>1A$4>2ws@1$2@1$1@1$0#k0>0@4$a^6^5^4^3>0@4$5?4segs^7^3^2>0@3$9$6@3$b^5^4@2$d+4@1$e@2$7@1$1@1$0#k0^3$8@4$5?4segs^8^5^4").
Proof. intros m m' X B A ws (W & MU & WM & HB) H Hc. eapply u32arr_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma u32arr_transport_sb : ltac2:(zQ "h01!iia!ikd!hlb!j4!h9!ju0!t4!hg3!iq3!hj9!sf!kj9!hsa!p2!jua!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$d>1c$4>2ws@1$2@1$1@1$0#k0>0@4$b^6^5^4^3>0@4$5?4segs^7@2$6^5^3^2>0@3$a$7@3$c^5^4@2$e+4@1$f@2$8@1$1@1$0#k0^3$9@4$5?4segs^8@2$6^7^5^4").
Proof. intros m m' X B c ws (W & MU & WM & HB) H Hc. eapply u32arr_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma u32arr_transport_sb0 : ltac2:(zQ "f1!iia!ikd!hlb!j4!ju0!hg3!iq3!hj9!sf!h9!kj9!hsa!p2!jua!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$9>1B@1$2$c>2ws@1$2@1$1@1$0#k0>0@4$a^5^4^3^2>0@4$4?4segs^6^4^2>0@3$8$5@3$b^4Z@2$d+4@1$e@2$6@1$1@1$0#k0^3$7@4$4?4segs^7^6^4").
Proof. intros m m' X B ws (W & MU & WM & HB) H Hc. eapply u32arr_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

Lemma u64arr_transport_lit : ltac2:(zQ "f1!iia!ikd!hlb!j4!h9!jv0!hg3!iq3!hj9!sf!kj9!hr6!p2!jua!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$c>1A$4>2ws@1$2@1$1@1$0#k0>0@4$a^6^5^4^3>0@4$5?4segs^7^3^2>0@3$9$6@3$b^5^4@2$d+8@1$e@2$7@1$1@1$0#k0^3$8@4$5?4segs^8^5^4").
Proof. intros m m' X B A ws (W & MU & WM & HB) H Hc. eapply u64arr_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma u64arr_transport_sb : ltac2:(zQ "h01!iia!ikd!hlb!j4!h9!jv0!t4!hg3!iq3!hj9!sf!kj9!hsa!p2!jua!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$d>1c$4>2ws@1$2@1$1@1$0#k0>0@4$b^6^5^4^3>0@4$5?4segs^7@2$6^5^3^2>0@3$a$7@3$c^5^4@2$e+8@1$f@2$8@1$1@1$0#k0^3$9@4$5?4segs^8@2$6^7^5^4").
Proof. intros m m' X B c ws (W & MU & WM & HB) H Hc. eapply u64arr_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma u64arr_transport_sb0 : ltac2:(zQ "f1!iia!ikd!hlb!j4!jv0!hg3!iq3!hj9!sf!h9!kj9!hsa!p2!jua!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$9>1B@1$2$c>2ws@1$2@1$1@1$0#k0>0@4$a^5^4^3^2>0@4$4?4segs^6^4^2>0@3$8$5@3$b^4Z@2$d+8@1$e@2$6@1$1@1$0#k0^3$7@4$4?4segs^7^6^4").
Proof. intros m m' X B ws (W & MU & WM & HB) H Hc. eapply u64arr_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

Lemma u8ro_transport_lit : ltac2:(zQ "e1!iia!ikd!hlb!j4!h9!jva!hg3!iq3!hj9!sf!kj9!hr6!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$c>1A$4>2xs@1$2@1$1@1$0#8>0@4$a^6^5^4^3>0@4$5?4segs^7^3^2>0@3$9$6@3$b^5^4@1$d@2$7@1$1@1$0#8^3$8@4$5?4segs^8^5^4").
Proof. intros m m' X B A xs (W & MU & WM & HB) H Hc. eapply u8ro_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma u8ro_transport_sb : ltac2:(zQ "f1!iia!ikd!hlb!j4!h9!jva!t4!hg3!iq3!hj9!sf!kj9!hsa!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$4>1B@1$2$d>1c$4>2xs@1$2@1$1@1$0#8>0@4$b^6^5^4^3>0@4$5?4segs^7@2$6^5^3^2>0@3$a$7@3$c^5^4@1$e@2$8@1$1@1$0#8^3$9@4$5?4segs^8@2$6^7^5^4").
Proof. intros m m' X B c xs (W & MU & WM & HB) H Hc. eapply u8ro_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma u8ro_transport_sb0 : ltac2:(zQ "e1!iia!ikd!hlb!j4!jva!hg3!iq3!hj9!sf!h9!kj9!hsa!p2!ipa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1X$9>1B@1$2$c>2xs@1$2@1$1@1$0#8>0@4$a^5^4^3^2>0@4$4?4segs^6^4^2>0@3$8$5@3$b^4Z@1$d@2$6@1$1@1$0#8^3$7@4$4?4segs^7^6^4").
Proof. intros m m' X B xs (W & MU & WM & HB) H Hc. eapply u8ro_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

End WithSegs.

Lemma munch_write_h : ltac2:(zQ "e1!iia!ikd!iq3!hlb!j4!h9!ki7!ipa!iu3!kk5!hqf!jnf!p2!kkf&>0@1$1@1$0#k0@1$4@1$1@1$0#8>1W@1$3$a>2m0~0>1m~0>1a$5>2bs@1$3@1$1@1$0#8>1X$5>1b$c>0@4$d^4@1$7@2$2@1$1@1$0#8^3^2^1>0@3$6^8^7^6>0@3$9^9^6@1$7@2$2@1$1@1$0#8^5@3$6^a^9@3$8^8@1$b^7^6").
Proof. intros W m0 m a bs X b (Ha & Hl & Hb) H Hin. apply munch_write; auto. Qed.

(* [comment removed for export] *)
Lemma store_lb_of_bound : ltac2:(zQ "a0!h9!t4!sa!hh2!hhe!hg3!hj9!q0!sf!ht4>1A$0>2sz$0>1k$0>1n$0>0@2$7@2$2Z^4@2$2@2$1^4^3@2$9+2+k0>0@3$8$5@2$4@2$3Z^3@2$3@2$1^3^2^4$6@2$2Z@2$1^6^4").
Proof. intros A sz k n [H1 H2] Hc. apply Bool.andb_true_iff in Hc. destruct Hc as [Hc _]. apply Z.leb_le in Hc. lia. Qed.
Lemma store_ub_of_bound : ltac2:(zQ "a0!h9!t4!sa!hh2!ht4!hhe!hg3!hj9!q0!sf>1A$0>2sz$0>1k$0>1n$0>0@2$8@2$2Z^4@2$2@2$1^4^3@2$4+2+k0>0@3$9$6@2$5@2$3Z^3@2$3@2$1^3^2^4$7@2$2@2$1@2$1^6^4^3@2$4+2+k0").
Proof. intros A sz k n [H1 H2] Hc. apply Bool.andb_true_iff in Hc. destruct Hc as [_ Hc]. apply Z.leb_le in Hc. lia. Qed.

(* [comment removed for export] *)
Record wdesc := WD { wd_l : option Z; wd_h : option Z; wd_lo : option Z; wd_hi : option Z }.
Definition wd_ok : ltac2:(zQ "20!h9!klb>1X$0>2lo$0>2hi$0>1w$1P") := ltac2:(zQ "a0!h9!sf!q6!q0!t4!km3!kma!kn2!kn9!klb\1X$0\2lo$0\2hi$0\1w$9@2$3@2$2@1$7^1\1l$0@3$1$0^4@2$4^5^1@2$3@2$2@1$5^1\1h$0@3$1$0^3@2$4^5^1@2$3@2$2@1$8^1\1v$0@3$1$0^4^1@2$2@1$6^1\1v$0@3$1$0^3^1").
Fixpoint wds_ok (X : Z) (W : list ivl) (D : list wdesc) : Prop :=
  match W, D with
  | [], [] => True
  | (lo, hi) :: W', w :: D' => wd_ok X lo hi w /\ wds_ok X W' D'
  | _, _ => False
  end.
(* [comment removed for export] *)
Definition chk_inside1 : ltac2:(zQ "40!hg3!h9!p2!klb>1w$3>1b$2>1n$1$0") := ltac2:(zQ "h10!h9!j4!hg3!hga!hh2!hhe!hh8!tf!ue!vc!p2!km3!kma!kn2!kn9!klb!t4\1w$f\1b$a\1n$0@2$6M1\1x@1$1$0$2@1$9^2\1d$0M1\1x@1$1$0$2@1$d^4\1l$0M1\1x@1$1$0$2@1$b^5\1h$0@2$5@2$4^2^3@2$4@2$h0^3^4^1$3$3$3M1\1x@1$1$0$2@1$7^2\1L$0M1\1x@1$1$0$2@1$8^3\1U$0M1\1x@1$1$0$2@1$e^5\2lo$0M1\1x@1$1$0$2@1$c^6\2hi$0@2$5@2$4^2^4@2$4^3^1$3$3$3$3").
Fixpoint chk_inside (D : list wdesc) (b : ibnd) (n : Z) : bool :=
  match D with [] => false | w :: D' => orb (chk_inside1 w b n) (chk_inside D' b n) end.

Lemma chk_inside_sound : ltac2:(zQ "d0!h9!hlb!hg3!hj9!sf!kk5!hqf!ko1!hka!p2!klb!koe!t4>1X$0>1a$0>1n$0>1b$9>1W@1$1$6>1D@1$1$a>0@4$8^6^5@2$c^5^4^3>0@3$b^7^3^2>0@3$4$2@3$7^3^5^6$3@3$5^5^8^7").
Proof.
  intros X a n [l h L U PQ] W. induction W as [|[lo hi] W IH]; intros [|w D] Hb Hok Hc; cbn in *;
    try discriminate; try contradiction.
  destruct Hok as [Hw HD]. apply Bool.orb_true_iff in Hc. destruct Hc as [Hc|Hc]; [left|right; eauto].
  destruct w as [wl wh wlo whi]. destruct Hb as (Hl & Hh & HL & HU & _). destruct Hw as (H1 & H2 & H3 & H4). cbn in *.
  apply Bool.orb_true_iff in Hc. destruct Hc as [Hc|Hc].
  - destruct l as [d|]; [|discriminate]. destruct wl as [wl|]; [|discriminate]. destruct wh as [wh|]; [|discriminate].
    cbn in *. apply Bool.andb_true_iff in Hc. destruct Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
  - destruct L as [L|]; [|discriminate]. destruct U as [U|]; [|discriminate].
    destruct wlo as [wlo|]; [|discriminate]. destruct whi as [whi|]; [|discriminate].
    cbn in *. apply Bool.andb_true_iff in Hc. destruct Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
Qed.

Lemma munch_write_wd : ltac2:(zQ "h31!iia!ikd!hlb!iq3!j4!h9!ki7!ipa!hg3!hj9!sf!iu3!hqf!jnf!ko1!p2!kkf!klb!koe&>0@1$1@1$0#k0@1$4@1$1@1$0#8>1W@1$2$c>2m0~0>1m~0>1a$5>2bs@1$2@1$1@1$0#8>1X$5>1b$f>1D@1$2$h1>0@4$h0^5@1$7@2$3@1$1@1$0#8^4^3^2>0@3$h2^4^9^2>0@3$6^a^9^8>0@3$a$8@3$e^4^5@1$7@2$3@1$1@1$0#8^7$9@3$6^c^b@3$b^a@1$d^9^8").
Proof.
  intros W m0 m a bs X b D (Ha & Hl & Hb) HD H Hc. apply munch_write; auto.
  eapply chk_inside_sound; eauto.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Module DietL2.
  Import Ltac2.
  Ltac2 rec is_pos_lit (c : constr) : bool :=
    lazy_match! c with xI ?p => is_pos_lit p | xO ?p => is_pos_lit p | xH => true | _ => false end.
  Ltac2 is_z_lit (c : constr) : bool :=
    lazy_match! c with Z0 => true | Zpos ?p => is_pos_lit p | Zneg ?p => is_pos_lit p | _ => false end.
  Ltac2 size_lit (sz : constr) : constr option :=
    let v := eval cbv beta iota zeta delta
      [cells_size csize length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes u32s u64s
       Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Z.add Pos.add] in $sz in
    if is_z_lit v then Some v else None.
  Ltac2 chunk_of (ty : constr) : (constr * constr) option :=
    lazy_match! ty with
    | rw_cells _ _ ?a ?cs => Some (a, constr:(Z.of_nat (cells_size $cs)))
    | ro_cells _ _ ?a ?cs => Some (a, constr:(Z.of_nat (cells_size $cs)))
    | bytes_at _ _ ?a ?bs => Some (a, constr:(Z.of_nat (@length byte $bs)))
    | u8arr _ _ ?a ?bs => Some (a, constr:(Z.of_nat (@length byte $bs)))
    | u8ro _ _ ?a ?bs => Some (a, constr:(Z.of_nat (@length byte $bs)))
    | u32arr _ _ ?a ?ws => Some (a, constr:((4 * Z.of_nat (@length word $ws))%Z))
    | u64arr _ _ ?a ?ws => Some (a, constr:((8 * Z.of_nat (@length word $ws))%Z))
    | _ => None
    end.
  Ltac2 hull () : unit :=
    let cands := List.map_filter (fun h => let (_, _, ty) := h in
        match chunk_of ty with
        | None => None
        | Some p => let (a, sz) := p in
            if is_z_lit a then match size_lit sz with Some s => Some (a, s) | None => None end else None
        end) (Control.hyps ()) in
    match cands with
    | [] => ltac1:(pose (diet_hull := @None (Z * Z)))
    | c :: rest =>
        let (a0, s0) := c in
        let smin := List.fold_left (fun acc c => let (a, _) := c in Std.eval_vm None constr:(Z.min $acc $a)) a0 rest in
        let emax := List.fold_left (fun acc c => let (a, s) := c in Std.eval_vm None constr:(Z.max $acc ($a + $s)%Z))
                      (Std.eval_vm None constr:(($a0 + $s0)%Z)) rest in
        let v := constr:(@Some (Z * Z) ($smin, $emax)) in
        ltac1:(v |- pose (diet_hull := v)) (Ltac1.of_constr v)
    end.
  Ltac2 hull1 () : unit := Control.enter hull.
End DietL2.
Ltac diet_hull k :=
  ltac2:(DietL2.hull1 ());
  lazymatch goal with D := ?v : option (Z * Z) |- _ => clear D; k v end.

(* [comment removed for export] *)
Ltac size_lit sz :=
  let v := eval cbv beta iota zeta delta
      [cells_size csize length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes u32s u64s
       Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Z.add Pos.add] in sz in
  lazymatch v with Z0 => v | Zpos _ => v | Zneg _ => v end.

(* [comment removed for export] *)
Ltac len_term bs :=
  let nT := constr:(Z.of_nat (@length byte bs)) in
  match nT with _ => size_lit nT | _ => nT end.

(* [comment removed for export] *)
Ltac zval a :=
  lazymatch a with
  | Z.add ?x ?y => let u := zval x in let v := zval y in eval vm_compute in (u + v)%Z
  | Z.sub ?x ?y => let u := zval x in let v := zval y in eval vm_compute in (u - v)%Z
  | _ => zlit_of a
  end.

(* [comment removed for export] *)
Ltac store_ctx_of_facts full a bs Ha Hl hullprover k :=
  let Hd := fresh "dHd" in let HPQ := fresh "dHPQ" in let SC := fresh "dSC" in
  let nT := constr:(Z.of_nat (@length byte bs)) in
  let n := len_term bs in
  sb_split a ltac:(fun X d pfd =>
    (* [comment removed for export] *)
    try (assert (Hd : dfact (a = (X + d)%Z)) by exact pfd);
    (* [comment removed for export] *)
    let av := match constr:(tt) with _ => let v := zval a in constr:(@Some Z v) | _ => constr:(@None Z) end in
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    let l := lazymatch goal with _ : dfact (a = (X + d)%Z) |- _ => constr:(@Some Z d) | _ => constr:(@None Z) end in
    let h := lazymatch l with
             | Some _ => match n with
                         | Z.of_nat _ => constr:(@None Z)
                         | _ => let e := eval vm_compute in (d + n)%Z in constr:(@Some Z e)
                         end
             | _ => constr:(@None Z)
             end in
    let U := lazymatch av with
             | Some ?v => match n with
                          | Z.of_nat _ => constr:(@None Z)
                          | _ => let e := eval vm_compute in (v + n)%Z in constr:(@Some Z e)
                          end
             | None => constr:(@None Z)
             end in
    let PQ := lazymatch goal with
              | _ : dfact (a + nT <= ?smin \/ ?emax <= a)%Z |- _ => constr:(@Some (Z * Z) (smin, emax))
              | _ => constr:(@None (Z * Z))
              end in
    let b := constr:(IB l h av U PQ) in
    assert (SC : store_ctx a nT X b);
    [ apply store_ctx_intro; [ exact Ha | exact Hl | ];
      cbv beta iota delta [ib_ok opt_holds ib_l ib_h ib_L ib_U ib_PQ];
      split; [ | split; [ | split; [ | split ] ] ];
      [ (* [comment removed for export] *) first [ exact I | lazymatch goal with |- ?G => lazymatch goal with Hf : dfact G |- _ => exact Hf end end ]
      | (* [comment removed for export] *) first [ exact I
                      | lazymatch goal with Hf : dfact (a = (X + d)%Z) |- _ =>
                          exact (@eq_trans Z (a + n)%Z (X + d + n)%Z (X + (d + n))%Z
                                 (@f_equal Z Z (fun t => (t + n)%Z) a (X + d)%Z Hf)
                                 (@eq_sym Z (X + (d + n))%Z (X + d + n)%Z (Z.add_assoc X d n)))
                        end ]
      | (* [comment removed for export] *) first [ exact I | lazymatch goal with |- (?v <= _)%Z => exact (Z.le_refl v) end ]
      | (* [comment removed for export] *) first [ exact I | lazymatch goal with |- (_ <= ?v)%Z => exact (Z.le_refl v) end ]
      | (* [comment removed for export] *) first [ exact I | lazymatch goal with |- ?G => lazymatch goal with Hf : dfact G |- _ => exact Hf end end ] ]
    | try clear HPQ; try clear Hd;
      k SC X b ]).

(* [comment removed for export] *)
Ltac store_ctx_pose full a bs k kfail :=
  let Ha := fresh "dHa" in let Hl := fresh "dHl" in
  let nT := constr:(Z.of_nat (@length byte bs)) in
  tryif (first [ lazymatch a with
                 | (?A0 + ?k)%Z =>
                     lazymatch goal with
                     | HB : (0 <= A0 /\ A0 + ?sz <= 2 ^ 64)%Z |- _ =>
                         pose proof (store_lb_of_bound A0 sz k nT HB (@eq_refl bool true)) as Ha
                     end
                 end
               | assert (Ha : (0 <= a)%Z) by lia ])
  then (
   tryif (first [ lazymatch a with
                  | (?A0 + ?k)%Z =>
                      lazymatch goal with
                      | HB : (0 <= A0 /\ A0 + ?sz <= 2 ^ 64)%Z |- _ =>
                          pose proof (store_ub_of_bound A0 sz k nT HB (@eq_refl bool true)) as Hl
                      end
                  end
                | assert (Hl : (a + nT <= 2^64)%Z) by (simpl_sizes; slia) ])
   then (store_ctx_of_facts full a bs Ha Hl ltac:(simpl_sizes; slia) k; clear Ha Hl)
   else (clear Ha; kfail))
  else kfail.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac clear_store_aux a :=
  repeat match goal with
  | H : store_ctx a _ _ _ |- _ => clear H
  | H : hull_fact a _ _ _ |- _ => clear H
  | H : hull_none a _ |- _ => clear H
  | H : dfact (a = _)%Z |- _ => clear H
  end.
(* [comment removed for export] *)
Ltac ensure_hull a nT prover :=
  lazymatch goal with
  | _ : hull_fact a nT _ _ |- _ => idtac
  | _ : hull_none a nT |- _ => fail
  | _ => let HF := fresh "dHF" in
         diet_hull ltac:(fun hv =>
           lazymatch hv with
           | Some (?smin, ?emax) =>
               first [ assert (HF : hull_fact a nT smin emax) by (unfold hull_fact; prover)
                     | pose proof (I : hull_none a nT) as HF; fail ]
           | None => pose proof (I : hull_none a nT) as HF; fail
           end)
  end.
(* [comment removed for export] *)
Ltac tr_hull H lem a nT A2 sz :=
  is_Zlit A2;
  lazymatch a with Z0 => fail | Zpos _ => fail | Zneg _ => fail | _ => idtac end;
  ensure_hull a nT ltac:(simpl_sizes; slia);
  lazymatch goal with
  | HF : hull_fact a nT ?P ?Q |- _ =>
      let s := size_lit sz in
      lazymatch eval vm_compute in (chk_hull P Q A2 s) with true => idtac end;
      apply lem in H; [ | exact HF | exact (@eq_refl bool true) ]
  end.
Ltac tr_lit H lem b A2 sz :=
  is_Zlit A2;
  let s := size_lit sz in
  lazymatch eval vm_compute in (chk_lit b A2 s) with true => idtac end;
  apply lem in H; [ | exact (@eq_refl bool true) ].
Ltac tr_lits H lem B A2 sz :=
  is_Zlit A2;
  let s := size_lit sz in
  lazymatch eval vm_compute in (chks_lit B A2 s) with true => idtac end;
  apply lem in H; [ | exact (@eq_refl bool true) ].
(* [comment removed for export] *)
Ltac tr_sb H lem lem0 chk b X A2 sz :=
  let s := size_lit sz in
  lazymatch A2 with
  | Z.add X ?c => is_Zlit c; lazymatch eval vm_compute in (chk b c s) with true => idtac end;
                 apply lem in H; [ | exact (@eq_refl bool true) ]
  | X => lazymatch eval vm_compute in (chk b 0%Z s) with true => idtac end;
         apply lem0 in H; [ | exact (@eq_refl bool true) ]
  end.

(* [comment removed for export] *)
Ltac tr1_sc segs m a bs SC X b H :=
  let nS := constr:(Z.of_nat (@length byte bs)) in
  lazymatch type of H with
  | bytes_at segs m ?A2 ?bs2 =>
      first [ tr_lit H (bytes_at_write_other_lit segs m a bs X b A2 bs2 SC) b A2 constr:(Z.of_nat (@length byte bs2))
            | tr_sb H (bytes_at_write_other_sb segs m a bs X b) (bytes_at_write_other_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte bs2))
            | tr_hull H (bytes_at_write_other_hl segs m a bs X b A2 bs2 SC) a nS A2 constr:(Z.of_nat (@length byte bs2))
            | apply (bytes_at_write_other_h segs m a bs X b A2 bs2 SC) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | wr_at segs m ?A2 ?n2 => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | rw_cells segs m ?A2 ?cs2 =>
      first [ tr_lit H (rw_cells_frame_lit segs m a bs X b A2 cs2 SC) b A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (rw_cells_frame_sb segs m a bs X b) (rw_cells_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (cells_size cs2))
            | tr_hull H (rw_cells_frame_hl segs m a bs X b A2 cs2 SC) a nS A2 constr:(Z.of_nat (cells_size cs2))
            | apply (rw_cells_frame_h segs m a bs X b A2 cs2 SC) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | ro_cells segs m ?A2 ?cs2 =>
      first [ tr_lit H (ro_cells_frame_lit segs m a bs X b A2 cs2 SC) b A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (ro_cells_frame_sb segs m a bs X b) (ro_cells_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (cells_size cs2))
            | tr_hull H (ro_cells_frame_hl segs m a bs X b A2 cs2 SC) a nS A2 constr:(Z.of_nat (cells_size cs2))
            | apply (ro_cells_frame_h segs m a bs X b A2 cs2 SC) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | u8arr segs m ?A2 ?xs =>
      first [ tr_lit H (u8arr_frame_lit segs m a bs X b A2 xs SC) b A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8arr_frame_sb segs m a bs X b) (u8arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte xs))
            | tr_hull H (u8arr_frame_hl segs m a bs X b A2 xs SC) a nS A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8arr_frame_h segs m a bs X b A2 xs SC) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | u32arr segs m ?A2 ?ws =>
      first [ tr_lit H (u32arr_frame_lit segs m a bs X b A2 ws SC) b A2 constr:((4 * Z.of_nat (@length word ws))%Z)
            | tr_sb H (u32arr_frame_sb segs m a bs X b) (u32arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:((4 * Z.of_nat (@length word ws))%Z)
            | tr_hull H (u32arr_frame_hl segs m a bs X b A2 ws SC) a nS A2 constr:((4 * Z.of_nat (@length word ws))%Z)
            | apply (u32arr_frame_h segs m a bs X b A2 ws SC) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | u64arr segs m ?A2 ?ws =>
      first [ tr_lit H (u64arr_frame_lit segs m a bs X b A2 ws SC) b A2 constr:((8 * Z.of_nat (@length word ws))%Z)
            | tr_sb H (u64arr_frame_sb segs m a bs X b) (u64arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:((8 * Z.of_nat (@length word ws))%Z)
            | tr_hull H (u64arr_frame_hl segs m a bs X b A2 ws SC) a nS A2 constr:((8 * Z.of_nat (@length word ws))%Z)
            | apply (u64arr_frame_h segs m a bs X b A2 ws SC) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | u8ro segs m ?A2 ?xs =>
      first [ tr_lit H (u8ro_frame_lit segs m a bs X b A2 xs SC) b A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8ro_frame_sb segs m a bs X b) (u8ro_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte xs))
            | tr_hull H (u8ro_frame_hl segs m a bs X b A2 xs SC) a nS A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8ro_frame_h segs m a bs X b A2 xs SC) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

(* [comment removed for export] *)
Ltac transport_chunks_sc segs m a bs SC X b :=
  repeat match goal with
  | H : bytes_at segs m _ _ |- _ => tr1_sc segs m a bs SC X b H
  | H : wr_at segs m _ _ |- _ => tr1_sc segs m a bs SC X b H
  | H : rw_cells segs m _ _ |- _ => tr1_sc segs m a bs SC X b H
  | H : ro_cells segs m _ _ |- _ => tr1_sc segs m a bs SC X b H
  | H : u8arr segs m _ _ |- _ => tr1_sc segs m a bs SC X b H
  | H : u32arr segs m _ _ |- _ => tr1_sc segs m a bs SC X b H
  | H : u64arr segs m _ _ |- _ => tr1_sc segs m a bs SC X b H
  | H : u8ro segs m _ _ |- _ => tr1_sc segs m a bs SC X b H
  end.

(* [comment removed for export] *)
Ltac transport_chunks_orig segs m a bs :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.
Ltac footprint_after_store_orig segs m a bs :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* [comment removed for export] *)
Ltac wd_off X e :=
  match e with
  | X => constr:(@Some Z 0%Z)
  | Z.add X ?c => let c' := zlit_of c in constr:(@Some Z c')
  | Z.sub X ?c => let c' := zlit_of c in let v := eval vm_compute in (- c')%Z in constr:(@Some Z v)
  | _ => constr:(@None Z)
  end.
Ltac wd_lit e := match e with _ => let v := zlit_of e in constr:(@Some Z v) | _ => constr:(@None Z) end.
Ltac wdesc_of X W :=
  lazymatch W with
  | nil => constr:(@nil wdesc)
  | cons (?lo, ?hi) ?W' =>
      let l := wd_off X lo in let h := wd_off X hi in
      let vlo := wd_lit lo in let vhi := wd_lit hi in
      let D' := wdesc_of X W' in constr:(@cons wdesc (WD l h vlo vhi) D')
  end.

Ltac footprint_after_store_sc segs m a bs SC X b :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ let D := wdesc_of X Wq in
              let n := size_lit constr:(Z.of_nat (@length byte bs)) in
              lazymatch eval vm_compute in (chk_inside D b n) with true => idtac end;
              let WDH := fresh "dWD" in
              assert (WDH : wds_ok X Wq D) by
                (cbv beta iota delta [wds_ok wd_ok opt_holds wd_l wd_h wd_lo wd_hi];
                 repeat match goal with |- _ /\ _ => split end;
                 first [ exact I | reflexivity | symmetry; apply Z.add_0_r ]);
              apply (munch_write_wd Wq mq m a bs X b D SC WDH) in MU; [ | exact (@eq_refl bool true) ];
              clear WDH
            | apply (munch_write_h Wq mq m a bs X b SC) in MU; [ | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ => apply (stk_write_h segs m loq hiq a bs X b SC) in STq
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac has_chunk_work segs m :=
  match goal with
  | _ : rw_cells segs m _ _ |- _ => idtac
  | _ : ro_cells segs m _ _ |- _ => idtac
  | _ : bytes_at segs m _ _ |- _ => idtac
  | _ : u8arr segs m _ _ |- _ => idtac
  | _ : u32arr segs m _ _ |- _ => idtac
  | _ : u64arr segs m _ _ |- _ => idtac
  | _ : u8ro segs m _ _ |- _ => idtac
  | _ : wr_at segs m _ _ |- _ => idtac
  end.
Ltac transport_chunks_default segs m a bs :=
  tryif has_chunk_work segs m then
    lazymatch goal with
    | SC : store_ctx a _ ?X ?b |- _ => transport_chunks_sc segs m a bs SC X b
    | _ => store_ctx_pose false a bs ltac:(fun SC X b => transport_chunks_sc segs m a bs SC X b)
                                  ltac:(transport_chunks_orig segs m a bs)
    end
  else idtac.
Ltac transport_chunks segs m a bs ::= transport_chunks_default segs m a bs.
(* [comment removed for export] *)
Ltac ensure_store_ctx a bs k kfail :=
  lazymatch goal with
  | SC : store_ctx a _ ?X ?b |- _ => k SC X b
  | _ => store_ctx_pose false a bs k kfail
  end.
(* [comment removed for export] *)
Ltac transport_chunk1_default segs m a bs H korig :=
  ensure_store_ctx a bs ltac:(fun SC X b => tr1_sc segs m a bs SC X b H) korig.
Ltac has_fp_work segs m :=
  match goal with
  | _ : munch _ _ m |- _ => idtac
  | _ : wmono segs _ m |- _ => idtac
  | _ : stk segs m _ _ |- _ => idtac
  end.
Ltac footprint_after_store segs m a bs :=
  tryif has_fp_work segs m then
    lazymatch goal with
    | SC : store_ctx a _ ?X ?b |- _ => footprint_after_store_sc segs m a bs SC X b
    | _ => store_ctx_pose false a bs ltac:(fun SC X b => footprint_after_store_sc segs m a bs SC X b)
                                  ltac:(footprint_after_store_orig segs m a bs)
    end
  else idtac.

Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          clear_store_aux (A + Z.of_nat kn)%Z;
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ib_of_call X lo hi PQ :=
  let l := wd_off X lo in let h := wd_off X hi in
  let L := wd_lit lo in let U := wd_lit hi in
  constr:(IB l h L U PQ).

(* [comment removed for export] *)
Ltac ivl_is_lit lo hi := is_zlit_term lo; is_zlit_term hi.

(* [comment removed for export] *)
Ltac ibs_of_call X W hv prover k :=
  lazymatch W with
  | nil => k constr:(@nil ibnd) ltac:(idtac)
  | cons (?lo, ?hi) ?W' =>
      let Hn := fresh "dCPQ" in
      (lazymatch hv with
       | Some (?smin, ?emax) =>
           first [ ivl_is_lit lo hi | assert (Hn : dfact (hi <= smin \/ emax <= lo)%Z) by (unfold dfact; prover) | idtac ]
       | None => idtac
       end);
      let PQ := lazymatch hv with
                | Some (?smin, ?emax) =>
                    lazymatch goal with
                    | _ : dfact (hi <= smin \/ emax <= lo)%Z |- _ => constr:(@Some (Z * Z) (smin, emax))
                    | _ => constr:(@None (Z * Z))
                    end
                | None => constr:(@None (Z * Z))
                end in
      let b := ib_of_call X lo hi PQ in
      ibs_of_call X W' hv prover ltac:(fun B' kc => k constr:(@cons ibnd b B') ltac:(kc; try clear Hn))
  end.

(* [comment removed for export] *)
Ltac base_of_ivls W :=
  lazymatch W with
  | nil => constr:(0%Z)
  | cons (?lo, ?hi) ?W' =>
      match constr:(tt) with
      | _ => let t := match constr:(tt) with _ => is_zlit_term lo end in
             match constr:(tt) with
             | _ => let t' := match constr:(tt) with _ => is_zlit_term hi end in base_of_ivls W'
             | _ => sb_split hi ltac:(fun X d pf => X)
             end
      | _ => sb_split lo ltac:(fun X d pf => X)
      end
  end.

(* [comment removed for export] *)
Ltac call_ctx_pose segs m m' MU WM prover k kfail :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  match constr:(tt) with
  | _ =>
    let X := base_of_ivls W in
    diet_hull ltac:(fun hv =>
      ibs_of_call X W hv prover ltac:(fun B kclear =>
        let CC := fresh "dCC" in
        tryif (assert (CC : call_ctx segs m m' X B);
               [ apply (call_ctx_intro segs W m m' X B MU WM);
                 cbv beta iota delta [ibs_ok ib_ok opt_holds ib_l ib_h ib_L ib_U ib_PQ];
                 repeat match goal with |- _ /\ _ => split end;
                 first [ exact I
                       | lazymatch goal with |- ?G => lazymatch goal with Hf : dfact G |- _ => exact Hf end end
                       | reflexivity | apply Z.le_refl | symmetry; apply Z.add_0_r ]
               | ])
        then (k CC X B; clear CC; kclear)
        else (kclear; kfail)))
  | _ => kfail
  end.

Ltac transport_after_call_orig segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac transport_after_call_cc segs m m' MU WM CC X B :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ tr_lits H (bytes_at_transport_lit segs m m' X B A2 bs2 CC) B A2 constr:(Z.of_nat (@length byte bs2))
            | tr_sb H (bytes_at_transport_sb segs m m' X B) (bytes_at_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte bs2))
            | apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lits H (rw_cells_transport_lit segs m m' X B A2 cs2 CC) B A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (rw_cells_transport_sb segs m m' X B) (rw_cells_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lits H (ro_cells_transport_lit segs m m' X B A2 cs2 CC) B A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (ro_cells_transport_sb segs m m' X B) (ro_cells_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u8arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8arr_transport_sb segs m m' X B) (u8arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u32arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u32arr_transport_sb segs m m' X B) (u32arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u64arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u64arr_transport_sb segs m m' X B) (u64arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u8ro_transport_lit segs m m' X B A2 xs CC) B A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8ro_transport_sb segs m m' X B) (u8ro_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac transport_after_call segs m m' MU WM :=
  call_ctx_pose segs m m' MU WM ltac:(lia)
    ltac:(fun CC X B => transport_after_call_cc segs m m' MU WM CC X B)
    ltac:(transport_after_call_orig segs m m' MU WM).

Ltac mem_after_store_opt ::=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac   (* [comment removed for export] *)
      end
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac destruct_exs PO :=
  let T := type of PO in let T' := eval hnf in T in
  lazymatch T' with
  | ex _ => let x := fresh "x" in destruct PO as [x PO]; destruct_exs PO
  | _ => idtac
  end.

Ltac destruct_ands PO :=
  lazymatch type of PO with
  | _ /\ _ => let H := fresh "PC" in destruct PO as [H PO]; destruct_ands PO
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac post_call segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
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
  (* [comment removed for export] *)
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      lazymatch eval vm_compute in (andb (Z.leb 0 n) (Z.ltb n 18446744073709551616)) with
      | true => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (apply bv_eq; vm_compute; reflexivity)
      | false => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end
  end).

Tactic Notation "call" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_call segs m ]
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac carve_frame n ST :=
  lazymatch type of ST with
  | stk ?segs ?m ?lo ?hi =>
      let junk := fresh "junk" in let FR := fresh "FR" in let ST' := fresh "ST" in
      destruct (stk_carve segs m lo hi n ST ltac:(lia)) as [ST' [junk FR]];
      clear ST; rename ST' into ST;
      let z := eval vm_compute in (Z.of_nat n) in
      change (Z.of_nat n) with z in ST, FR;
      (* [comment removed for export] *)
      repeat match type of FR with
      | context [Z.sub (Z.add ?b ?c) ?d] => is_Zlit c; is_Zlit d; let v := eval vm_compute in (c - d)%Z in
           replace (Z.sub (Z.add b c) d) with (Z.add b v) in * by lia
      | context [Z.sub ?b ?d] => is_Zlit d; let v := eval vm_compute in (- d)%Z in
           replace (Z.sub b d) with (Z.add b v) in * by lia
      end
  end.

(* [comment removed for export] *)
Fixpoint mk_CB_cells (sizes : list nat) (bs : list byte) : list cell :=
  match sizes with
  | [] => []
  | s :: sizes' => CB s (firstn s bs) :: mk_CB_cells sizes' (skipn s bs)
  end.

Fixpoint sum_nat (l : list nat) : nat := match l with [] => 0 | x :: l' => x + sum_nat l' end.

Lemma mk_CB_cells_wf : ltac2:(zQ "90!hlb!kp7!iia!ikd!iq3!sf!kpd!kq9!kr7>5sizes@1$0$1>2bs@1$0@1$3@1$2#8>0@3$5$1@2$4@1$3@1$2#8^1@1$8^2@1$6@2$7^3^2").
Proof.
  induction sizes as [|s sizes IH]; intros bs H; cbn; [exact I|].
  cbn in H. split.
  - rewrite firstn_length. lia.
  - apply IH. rewrite skipn_length. lia.
Qed.

Lemma mk_CB_cells_bytes : ltac2:(zQ "90!hlb!iia!ikd!kp7!sf!iq3!ks1!kq9!kr7>5sizes@1$0$3>2bs@1$0@1$2@1$1#8>0@3$4$3@2$5@1$2@1$1#8^1@1$8^2@3$4@1$0@1$2@1$1#8@1$6@2$7^3^2^2").
Proof.
  induction sizes as [|s sizes IH]; intros bs H; cbn in *.
  - destruct bs; [reflexivity| cbn in H; lia].
  - rewrite IH by (rewrite skipn_length; lia). apply firstn_skipn.
Qed.

Lemma mk_CB_cells_size : ltac2:(zQ "80!hlb!kp7!sf!iia!jj7!kq9!kr7!ikd>5sizes@1$0$1>2bs@1$0@1$7@1$3#8@3$2$1@1$4@2$5^2^1@1$6^2").
Proof. induction sizes; intros; cbn; [reflexivity|]. rewrite IHsizes. reflexivity. Qed.

Lemma rw_cells_split_CB : ltac2:(zQ "f0!jif!hlb!kt0!kp7!iia!ikd!ioe!kt6!j4!sf!h9!lh2!lhd!kq9!kr7>4segs@1$1$b>1m>0@1$5@1$4#k0@1$8@1$5@1$4#8>1A$a>3pre@1$1$0>1n$3>4junk@1$1@1$5@1$4#8>4post@1$1$0>5sizes@1$1$3>0@4$6^8^7^6@3$2$0^5@3$7$0@2$c^4^3^2>0@3$9$3@1$e^2^5@4$6^a^9^8@3$2$0^7@3$2$0@2$d^3^5^4").
Proof.
  intros segs m A pre n junk post sizes [[Hwf Hb] Hw] Hs.
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  assert (L : length junk = sum_nat sizes) by lia.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [apply mk_CB_cells_wf; exact L| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite mk_CB_cells_bytes by exact L. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite mk_CB_cells_size, Hs. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_merge : ltac2:(zQ "d0!jif!hlb!kt0!iia!ioe!ikd!kt6!j4!h9!lh2!lhd!ks1!jj7>4segs@1$1$9>1m>0@1$5@1$3#k0@1$7@1$5@1$3#8>1A$8>3pre@1$1$0>3mid@1$1$0>4post@1$1$0>0@4$4^6^5^4@3$2$0^3@3$2$0^2^1@4$4^7^6^5@3$2$0^4@3$6$0@2$a@1$c^3@1$b^3^2").
Proof.
  intros segs m A pre mid post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 H23]. apply cells_wf_app in H23. destruct H23 as [H2 H3].
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. cbn. split; [apply cells_bytes_length; exact H2| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes]. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize]. exact Hw.
Qed.

(* [comment removed for export] *)
Ltac finish :=
  apply evt_done;
  lazymatch goal with |- ?P ?ms => try unfold P end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ reflexivity | ]
  | |- _ = _ => reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
Ltac release_frame FR ST hi :=
  eapply stk_release in FR; [ | exact ST | lia ];
  clear ST; rename FR into ST;
  cbn [cells_size csize Nat.add] in ST;
  lazymatch type of ST with
  | stk ?segs ?m ?lo ?hi' => replace hi' with hi in ST by lia
  end.

(* [comment removed for export] *)
Ltac store_done :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     | _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
     end);
    (* [comment removed for export] *)
    try (lazymatch goal with
    | HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
        apply (mem_inv_store segs m (wa E) bs) in HI;
        [ | first [ exact HS
                  | replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
                    first [ exact HS | simpl_sizes; exact HS ] ] ]
    end);
    (* [comment removed for export] *)
    let HBa := fresh "HBarr" in
    try (let X := lazymatch E with Z.add (Z.add ?X _) _ => X | Z.add ?X _ => X | _ => E end in
         first [ lazymatch goal with
                 | H : u32arr segs m X ?xs |- _ => pose proof (u32arr_bound segs m X xs H) as HBa
                 | H : u8arr segs m X ?xs |- _ => pose proof (u8arr_bound segs m X xs H) as HBa
                 | H : u64arr segs m X ?xs |- _ => pose proof (u64arr_bound segs m X xs H) as HBa
                 end
               | lazymatch E with Z.add (Z.add ?X2 _) _ =>
                   lazymatch goal with
                   | H : u32arr segs m X2 ?xs |- _ => pose proof (u32arr_bound segs m X2 xs H) as HBa
                   | H : u8arr segs m X2 ?xs |- _ => pose proof (u8arr_bound segs m X2 xs H) as HBa
                   | H : u64arr segs m X2 ?xs |- _ => pose proof (u64arr_bound segs m X2 xs H) as HBa
                   end
                 end ]);
    transport_chunks segs m E bs; footprint_after_store segs m E bs; clear_store_aux E;
    try clear HBa;
    let m' := fresh "m" in
    remember (write_to_mem m (wa E) bs) as m' eqn:Heqm;
    clear Heqm;
    repeat match goal with
    | H : store_ok segs m _ _ = true |- _ => clear H
    | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
    end;
    try clear m
  end.

(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Export StepFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
(* [comment removed for export] *)
