(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7 V_Ma6xg V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcp0e6 AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpya4 AIcp3q7 AIcpii0 AIcpinq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp.AIcpwd0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpii0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpinq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_La0bg.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | first [ lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; nia ] ].
(* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stA (s : vstate) : Z :=
  match s with
  | S_Start => 0x22c80 | S_BOM => 0x22cc0 | S_TestXml => 0x22d00 | S_NotXml => 0x22dc0 | S_NotMyTag => 0x22e60
  | S_NxtTag => 0x22ce0 | S_StartTag => 0x22d20 | S_Comment => 0x22ea0 | S_CommentESI => 0x22f00 | S_CDATA => 0x22f80
  | S_end_ESITag => 0x22fc0 | S_ESITag => 0x22fe0 | S_ESI_Include => 0x23000 | S_ESI_Remove => 0x23120
  | S_ESI_Comment => 0x23140 | S_ESI_Bogon => 0x23220 | S_InTag => 0x23100 | S_TagError => 0x23080 | S_Attr => 0x23320
  | S_SkipAttribute => 0x23420 | S_AttrGetValue => 0x234a0 | S_AttrDelim => 0x23440 | S_AttrValue => 0x234c0
  | S_Until => 0x22ee0 | S_Match => 0x22ca0 | S_MatchBuf => 0x23640
  end.

(* [comment removed for export] *)
Definition stvarA (s : vstate) : Z :=
  match s with
  | S_Start => 0xa8800 | S_BOM => 0xa8820 | S_CommentESI => 0xa8840 | S_NxtTag => 0xa8860
  | S_Comment => 0xa8880 | S_end_ESITag => 0xa88a0 | S_ESITag => 0xa88c0 | S_CDATA => 0xa88e0
  | S_NotMyTag => 0xa8900 | S_ESI_Include => 0xa8920 | S_ESI_Remove => 0xa8940 | S_ESI_Comment => 0xa8960
  | S_ESI_Bogon => 0xa8980 | S_AttrGetValue => 0xa89a0 | S_SkipAttribute => 0xa89c0
  | _ => 0
  end.

Definition VIA : vimg := {|
  vi_bss_vsc := 0x5e7240;
  vi_bss_cp := 0x5e7260;
  vi_cb := 0x8fda4;
  vi_do_include := 0x8e958; vi_do_remove := 0x8f4e8; vi_do_comment := 0x8f64c;
  vi_st := stA;
  vi_stvar := stvarA;
  vi_wsid := 0x217c0; vi_url := 0x217e0; vi_empty := 0x22bc0; vi_arrow := 0x22ec0; vi_cdata_end := 0x22fa0;
  vi_tbl_bom := TBL_bom; vi_tbl_starttag := TBL_starttag; vi_tbl_esi := TBL_esi; vi_tbl_attr_include := TBL_attr_include
|}.

(* [comment removed for export] *)
Definition GOTA_vct    : Z := 0xa97f0.   (* [comment removed for export] *)
Definition GOTA_vsc    : Z := 0xa97f8.   (* [comment removed for export] *)
Definition GOTA_cp     : Z := 0xa9800.   (* [comment removed for export] *)
Definition GOTA_memset : Z := 0xa96d8.   (* [comment removed for export] *)
Definition VCT_TYPTABA : Z := 0x243c0.
Definition MEMSET_ICPT_ENTRY : Z := 0x574f4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition clookup (a : Z) (l : list (Z * list byte)) : option (list byte) :=
  match find (fun c => Z.eqb (fst c) a) l with Some c => Some (snd c) | None => None end.

Lemma clookup_In : forall a l bs, clookup a l = Some bs -> In (a, bs) l.
Proof.
  intros a l bs H. unfold clookup in H.
  destruct (find (fun c => Z.eqb (fst c) a) l) as [[a' bs']|] eqn:E; [|discriminate].
  injection H as <-. apply find_some in E as [HIn Heq]. cbn in Heq. apply Z.eqb_eq in Heq. subst a'. exact HIn.
Qed.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma consts_lookup : forall v a bs,
  consts_hold LPA v -> clookup a (cl_consts LPA) = Some bs -> bytes_at rsegs v a bs.
Proof.
  intros v a bs CH HL. unfold consts_hold in CH. rewrite Forall_forall in CH.
  exact (CH (a, bs) (clookup_In _ _ _ HL)).
Qed.

End CEIL.

(* [comment removed for export] *)
Ltac consts_cell CH a :=
  let H := fresh "CC" in
  pose proof (consts_lookup _ a _ CH ltac:(vm_compute; reflexivity)) as H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cells.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variable v : mem.
  Hypothesis CH : consts_hold LPA v.

  #[using="CH"] Lemma got_vct_cell : ro_cells rsegs v GOTA_vct [C8 (Z_to_bv 64 VCT_TYPTABA)].
  Proof. apply ro_C8_of_bytes. apply (consts_lookup v _ _ CH). vm_compute. reflexivity. Qed.

  #[using="CH"] Lemma got_vsc_cell : ro_cells rsegs v GOTA_vsc [C8 (Z_to_bv 64 (vi_bss_vsc VIA))].
  Proof. apply ro_C8_of_bytes. apply (consts_lookup v _ _ CH). vm_compute. reflexivity. Qed.

  #[using="CH"] Lemma got_cp_cell : ro_cells rsegs v GOTA_cp [C8 (Z_to_bv 64 (vi_bss_cp VIA))].
  Proof. apply ro_C8_of_bytes. apply (consts_lookup v _ _ CH). vm_compute. reflexivity. Qed.

  #[using="CH"] Lemma got_memset_cell : ro_cells rsegs v GOTA_memset [C8 (Z_to_bv 64 MEMSET_ICPT_ENTRY)].
  Proof. apply ro_C8_of_bytes. apply (consts_lookup v _ _ CH). vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="CH"] Lemma map_cells_of_consts : map_cells v.
  Proof.
    apply map_cells_of_bytes; (apply (consts_lookup v _ _ CH); vm_compute; reflexivity).
  Qed.

  (* [comment removed for export] *)
  #[using="CH"] Lemma set_shadow_cells_of_consts : set_shadow_cells v.
  Proof. split; apply ro_C8_of_bytes; (apply (consts_lookup v _ _ CH); vm_compute; reflexivity). Qed.

  #[using="CH"] Lemma asan_memset_cells_of_consts : asan_memset_cells v.
  Proof.
    split; [|split; [|split; [| exact map_cells_of_consts]]];
      [apply ro_C8_of_bytes| apply ro_C1_of_bytes| apply ro_C8_of_bytes];
      (apply (consts_lookup v _ _ CH); vm_compute; reflexivity).
  Qed.

  #[using="CH"] Lemma asan_memcpy_cells_of_consts : asan_memcpy_cells v.
  Proof.
    split; [|split; [|split; [| exact map_cells_of_consts]]];
      [apply ro_C8_of_bytes| apply ro_C1_of_bytes| apply ro_C8_of_bytes];
      (apply (consts_lookup v _ _ CH); vm_compute; reflexivity).
  Qed.

  #[using="CH"] Lemma strlen_icpt_cells_of_consts : strlen_icpt_cells v.
  Proof.
    eapply (strlen_icpt_cells_of_bytes v pa_common_flags_bytes);
      [ .. | reflexivity | exact map_cells_of_consts];
      (apply (consts_lookup v _ _ CH); vm_compute; reflexivity).
  Qed.

  (* [comment removed for export] *)
  #[using="CH"] Lemma strcpy_icpt_cells_of_consts : strcpy_icpt_cells v.
  Proof.
    eapply (strcpy_icpt_cells_of_bytes v pa_asan_flags_bytes);
      [ .. | reflexivity | | exact map_cells_of_consts];
      (apply (consts_lookup v _ _ CH); vm_compute; reflexivity).
  Qed.
End Cells.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition gdesc_eqb (d e : Z * Z * Z) : bool :=
  match d, e with (b, s, r), (b', s', r') => Z.eqb b b' && Z.eqb s s' && Z.eqb r r' end%bool.

Lemma gdesc_eqb_eq : forall d e, gdesc_eqb d e = true -> d = e.
Proof.
  intros [[b s] r] [[b' s'] r'] H. cbn in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. congruence.
Qed.

Lemma gdesc_in_b : forall d, existsb (gdesc_eqb d) pa_gdescs = true -> In d pa_gdescs.
Proof.
  intros d H. apply existsb_exists in H as (e & HIn & Heq). apply gdesc_eqb_eq in Heq. subst e. exact HIn.
Qed.

(* [comment removed for export] *)
Ltac gdesc_in := apply gdesc_in_b; vm_compute; reflexivity.

(* [comment removed for export] *)
Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma global_shadow : forall v b s r,
  consts_hold LPA v -> In (b, s, r) pa_gdescs ->
  bytes_at rsegs v (sh b) (shpat s ++ repeat (Z_to_bv 8 0xf9) (Z.to_nat ((r - (s + 7) / 8 * 8) / 8))).
Proof.
  intros v b s r CH HIn. unfold consts_hold in CH.
  change (cl_consts LPA) with (pa_cells ++ pa_gshadow ++ pa_zshadow) in CH.
  apply Forall_app in CH as [_ CH]. apply Forall_app in CH as [CH _].
  unfold pa_gshadow in CH. rewrite Forall_map, Forall_forall in CH.
  exact (CH (b, s, r) HIn).
Qed.

Lemma global_shadow_pat : forall v b s r,
  consts_hold LPA v -> In (b, s, r) pa_gdescs -> bytes_at rsegs v (sh b) (shpat s).
Proof.
  intros v b s r CH HIn. pose proof (global_shadow v b s r CH HIn) as X.
  apply (proj1 (bytes_at_app rsegs v (sh b) _ _)) in X. exact (proj1 X).
Qed.

Definition gdesc_okb (d : Z * Z * Z) : bool :=
  match d with (b, s, r) => (b mod 32 =? 0) && (0 <=? s) && (s <=? r) && (r mod 32 =? 0) && (0x10000 <=? b) && (b + r <=? 0x60a000) end.
Lemma gdesc_okb_all : forallb gdesc_okb pa_gdescs = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
Lemma gdesc_facts : forall b s r, In (b, s, r) pa_gdescs -> b mod 32 = 0 /\ 0 <= s <= r /\ r mod 32 = 0 /\ 0x10000 <= b /\ b + r <= 0x60a000.
Proof.
  (* [comment removed for export] *)
  intros b s r HIn. pose proof (proj1 (forallb_forall gdesc_okb pa_gdescs) gdesc_okb_all (b, s, r) HIn) as H.
  unfold gdesc_okb in H. cbv beta iota in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.eqb_eq in H4. apply Z.leb_le in H5. apply Z.leb_le in H6.
  exact (conj H1 (conj (conj H2 H3) (conj H4 (conj H5 H6)))).
Qed.

Lemma shadowed_global : forall v b s r a n,
  consts_hold LPA v -> In (b, s, r) pa_gdescs -> b <= a -> a + n <= b + s -> shadowed LPA v a n.
Proof.
  intros v b s r a n CH HIn Ha Hn. pose proof (gdesc_facts b s r HIn) as (AL & SZ & _ & LO & HI).
  exists b, s. split; [exact (global_shadow_pat v b s r CH HIn)|].
  pose proof alloc_ceiling_num as ACV.
  split.
  { pose proof (Z.div_mod b 32 ltac:(lia)) as D. rewrite AL, Z.add_0_r in D. rewrite D.
    replace (32 * (b / 32)) with ((4 * (b / 32)) * 8) by lia. apply Z.mod_mul. lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma shadowed_bss_vsc : forall v, consts_hold LPA v -> shadowed LPA v (vi_bss_vsc VIA) 8.
Proof. intros v CH. eapply (shadowed_global v 0x5e7240 8 32); [exact CH| gdesc_in| cbn; lia| cbn; lia]. Qed.

Lemma shadowed_bss_cp : forall v, consts_hold LPA v -> shadowed LPA v (vi_bss_cp VIA) 8.
Proof. intros v CH. eapply (shadowed_global v 0x5e7260 8 32); [exact CH| gdesc_in| cbn; lia| cbn; lia]. Qed.

(* [comment removed for export] *)

Lemma shadowed_empty : forall v, consts_hold LPA v -> shadowed LPA v (vi_empty VIA) 1.
Proof. intros v CH. eapply (shadowed_global v 0x22bc0 1 32); [exact CH| gdesc_in| cbn; lia| cbn; lia]. Qed.

End CEIL2.

(* [comment removed for export] *)
Section Vis.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma global_shadow_word_visible : forall A m md b s r a,
    ainv A m md -> In (b, s, r) pa_gdescs -> b <= a < b + r -> ~ pa_static a ->
    mapped (aview A m) (sh a - sh a mod 8) 8.
  Proof.
    intros A m md b s r a AI0 HIn Ha NS. pose proof (gdesc_facts b s r HIn) as (_ & _ & _ & LO & HI).
    apply (as_shadow_visible LPA A m md a AI0).
    - left. unfold kLowMemEnd. lia.
    - intros O. destruct (as_owned_where LPA A m md a AI0 O) as [S|[_ NI]]; [exact (NS S)|].
      apply NI. unfold in_image. cbn. lia.
    - left. unfold in_image. cbn. lia.
  Qed.
End Vis.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vepvars_ok (v : mem) : Prop :=
  forall S, stvarA S <> 0 -> ro_cells rsegs v (stvarA S) [C8 (Z_to_bv 64 (stA S))].

Definition img_tabs (v : mem) : Prop :=
     ro_cells rsegs v TBL_bom (mtab_cells tbl_bom)
  /\ ro_cells rsegs v TBL_attr_include (mtab_cells tbl_attr_include)
  /\ ro_cells rsegs v TBL_esi (mtab_cells tbl_esi)
  /\ ro_cells rsegs v TBL_starttag (mtab_cells tbl_starttag)
  /\ vepvars_ok v.

Lemma ro_cells_of_bytes_eq : forall (v : mem) a bs cs,
  bytes_at rsegs v a bs -> cells_wf cs -> cells_bytes cs = bs -> ro_cells rsegs v a cs.
Proof. intros v a bs cs B W E. split; [exact W|]. rewrite E. exact B. Qed.

Section CEIL3.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma vepvars_of_consts : forall v, consts_hold LPA v -> vepvars_ok v.
Proof.
  intros v CH S NZ; destruct S; cbn [stvarA stA] in *; try (exfalso; apply NZ; reflexivity);
    apply ro_C8_of_bytes; (apply (consts_lookup v _ _ CH); vm_compute; reflexivity).
Qed.

Lemma img_tabs_of_consts : forall v, consts_hold LPA v -> img_tabs v.
Proof.
  intros v CH. split; [|split; [|split; [|split; [| exact (vepvars_of_consts v CH)]]]];
    (eapply ro_cells_of_bytes_eq; [apply (consts_lookup v _ _ CH); vm_compute; reflexivity
                                  | cbn; repeat split; exact I || exact Logic.I
                                  | vm_compute; reflexivity]).
Qed.

End CEIL3.

Section Tabs.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Lemma img_tabs_ainv : forall A m md, ainv A m md -> img_tabs (aview A m).
  Proof. intros A m md AI0. exact (img_tabs_of_consts _ (consts_hold_ainv LPA A m md AI0)). Qed.

End Tabs.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL4.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition cenv (v : mem) : Prop :=
  consts_hold LPA v /\ (forall a, 0x10000 <= a < 0x60a000 -> ~ pa_static a -> mapped v (sh a - sh a mod 8) 8).

End CEIL4.

Section CEnv.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma cenv_intro : forall A m md, ainv A m md -> cenv (aview A m).
  Proof.
    intros A m md AI0. split; [exact (consts_hold_ainv LPA A m md AI0)|].
    intros a Ha NS. apply (as_shadow_visible LPA A m md a AI0).
    - left. unfold kLowMemEnd. lia.
    - intros O. destruct (as_owned_where LPA A m md a AI0 O) as [S|[_ NI]]; [exact (NS S)|].
      apply NI. unfold in_image. cbn. lia.
    - left. unfold in_image. cbn. lia.
  Qed.
End CEnv.

(* [comment removed for export] *)
Definition CONSTS_TOP : Z := 0x800d0000.         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition const_free_ivl (iv : Z * Z) : Prop :=
  CONSTS_TOP <= fst iv \/ (0x5e7210 <= fst iv /\ snd iv <= 0x5e7b80)
  \/ (0x60a000 <= fst iv /\ snd iv <= 2147450880) \/ snd iv <= 0x10000.

Lemma consts_const_free :
  Forall (fun c => (fst c + Z.of_nat (length (snd c)) <= 0x5e7210 \/ 0x5e7b80 <= fst c) /\ fst c + Z.of_nat (length (snd c)) <= CONSTS_TOP
                   /\ 0x10000 <= fst c /\ (fst c + Z.of_nat (length (snd c)) <= 0x60a000 \/ 2147450880 <= fst c))
         (cl_consts LPA).
Proof.
  apply Forall_forall. intros c Hc.
  assert (B : forallb (fun c => ((fst c + Z.of_nat (length (snd c)) <=? 0x5e7210) || (0x5e7b80 <=? fst c))
                               && (fst c + Z.of_nat (length (snd c)) <=? CONSTS_TOP)
                               && (0x10000 <=? fst c)
                               && ((fst c + Z.of_nat (length (snd c)) <=? 0x60a000) || (2147450880 <=? fst c)))%bool (cl_consts LPA) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B c Hc). cbn beta in B.
  apply andb_prop in B as [B B4]. apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2].
  apply Z.leb_le in B2. apply Z.leb_le in B3.
  apply Bool.orb_prop in B1 as [B1|B1]; apply Z.leb_le in B1;
  apply Bool.orb_prop in B4 as [B4|B4]; apply Z.leb_le in B4; lia.
Qed.

Section CEIL5.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma consts_hold_munch : forall W m m',
  consts_hold LPA m -> munch W m m' -> Forall const_free_ivl W -> consts_hold LPA m'.
Proof.
  intros W m m' CH MU FW. unfold consts_hold in *. rewrite Forall_forall in CH |- *.
  pose proof consts_const_free as CF. rewrite Forall_forall in CF.
  intros c Hc. specialize (CH c Hc). destruct (CF c Hc) as (C1 & C2 & C3 & C4).
  eapply bytes_at_munch; [exact CH| exact MU|].
  intros a Ha. clear CH Hc MU. induction W as [|[lo hi] W IH]; [exact I|].
  cbn. apply Forall_cons_iff in FW as [F1 FW]. split; [| exact (IH FW)].
  unfold const_free_ivl in F1. cbn in F1. lia.
Qed.

Lemma const_free_outside : forall W a, Forall const_free_ivl W ->
  2147450880 <= a < CONSTS_TOP -> outside W a.
Proof.
  intros W a FW Ha. unfold CONSTS_TOP in *. induction W as [|[lo hi] W IH]; [exact I|].
  cbn. apply Forall_cons_iff in FW as [F1 FW]. split; [| exact (IH FW)].
  unfold const_free_ivl, CONSTS_TOP in F1. cbn in F1. lia.
Qed.

Lemma cenv_munch : forall W m m',
  cenv m -> munch W m m' -> Forall const_free_ivl W -> cenv m'.
Proof.
  intros W m m' [CH VIS] MU FW. split; [eapply consts_hold_munch; eauto|].
  intros a Ha NS. eapply mapped_munch; [exact MU| | | | exact (VIS a Ha NS)].
  - unfold sh, kShadowOffset. pose proof (Z.mod_pos_bound (a / 8 + 2147450880) 8 ltac:(lia)).
    assert (0 <= a / 8) by (apply Z.div_pos; lia). lia.
  - unfold sh, kShadowOffset. pose proof (Z.mod_pos_bound (a / 8 + 2147450880) 8 ltac:(lia)).
    assert (a / 8 <= 0x60a000 / 8) by (apply Z.div_le_mono; lia). change (0x60a000 / 8) with 791552 in *. lia.
  - intros i Hi. apply const_free_outside; [exact FW|]. unfold sh, kShadowOffset, CONSTS_TOP.
    pose proof (Z.mod_pos_bound (a / 8 + 2147450880) 8 ltac:(lia)).
    assert (0x10000 / 8 <= a / 8) by (apply Z.div_le_mono; lia).
    assert (a / 8 <= 0x609fff / 8) by (apply Z.div_le_mono; lia).
    change (0x10000 / 8) with 8192 in *. change (0x609fff / 8) with 791551 in *. lia.
Qed.

End CEIL5.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shadow_ok_of_shpat : forall m p n a k,
  bytes_at rsegs m (sh p) (shpat n) -> (p mod 8 = 0)%Z -> (0 <= p)%Z ->
  (p <= a)%Z -> (a + k <= p + n)%Z -> (1 <= k)%Z ->
  shadow_ok m a k.
Proof.
  intros m p n a k SH AL P0 LO HI K.
  assert (N0 : (0 <= n)%Z) by lia.
  destruct SH as (S0 & S1 & S2). rewrite (shpat_length n N0) in S1.
  assert (LEN : Z.of_nat (length (shpat n)) = ((n + 7) / 8)%Z) by (apply shpat_length; lia).
  set (i0 := (a / 8 - p / 8)%Z). set (i1 := ((a + k - 1) / 8 - p / 8)%Z).
  assert (R : (0 <= i0 <= i1)%Z /\ (i1 <= (n - 1) / 8)%Z /\ ((n - 1) / 8 < (n + 7) / 8)%Z /\ ((n - 1) / 8 <= n / 8)%Z
              /\ (sh p + i0 = a / 8 + shadow_off)%Z).
  { unfold i0, i1, sh, kShadowOffset, shadow_off. Z.div_mod_to_equations. lia. }
  destruct R as (R0 & R1 & R1' & R1'' & R2).
  assert (CASE : (i1 < n / 8)%Z \/ (i1 = n / 8 /\ n mod 8 <> 0 /\ (a + k - 1) mod 8 < n mod 8 <= 7)%Z).
  { unfold i0, i1 in *. Z.div_mod_to_equations. lia. }
  exists (Z.to_nat (i1 - i0)), (if Z_lt_le_dec i1 (n / 8) then 0%Z else (n mod 8)%Z).
  split; [lia|]. split.
  - split; [unfold shadow_off; lia|]. split.
    { rewrite length_app, zeros_length. cbn [length]. lia. }
    intros j Hj. rewrite length_app, zeros_length in Hj. cbn [length] in Hj.
    rewrite <- R2.
    replace (sh p + i0 + Z.of_nat j)%Z with (sh p + Z.of_nat (Z.to_nat (i0 + Z.of_nat j)))%Z by lia.
    rewrite (S2 (Z.to_nat (i0 + Z.of_nat j))) by (apply Nat2Z.inj_lt; rewrite LEN; lia).
    destruct (Nat.eq_dec j (Z.to_nat (i1 - i0))) as [Ej | Nj].
    + (* [comment removed for export] *)
      rewrite nth_error_app2 by (rewrite zeros_length; lia). rewrite zeros_length.
      replace (j - Z.to_nat (i1 - i0))%nat with 0%nat by lia. cbn [nth_error].
      destruct (Z_lt_le_dec i1 (n / 8)) as [LT | GE].
      * rewrite shpat_nth_full; [reflexivity | lia | lia].
      * destruct CASE as [LT | (E1 & M & _)]; [lia|].
        replace (Z.to_nat (i0 + Z.of_nat j)) with (Z.to_nat (n / 8)) by lia.
        rewrite shpat_nth_tail; [reflexivity | lia | exact M].
    + rewrite nth_error_app1 by (rewrite zeros_length; lia). rewrite zeros_nth by lia.
      rewrite shpat_nth_full; [reflexivity | lia | lia].
  - destruct (Z_lt_le_dec i1 (n / 8)) as [LT | GE]; [left; reflexivity | right].
    destruct CASE as [LT | (E1 & M & B)]; [lia | exact B].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation mtab_strings := (mtab_strings rsegs).


Section Ranges.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma live_shadow_word : forall A m md p n a,
    ainv A m md -> a_live A p = Some n -> p <= a < p + n -> mapped (aview A m) (sh a - sh a mod 8) 8.
  Proof.
    intros A m md p n a AI0 LV Ha.
    destruct (as_live_ok LPA A m md p n AI0 LV) as (N0 & AL & LO & HI & IMG & MP & NO & _).
    pose proof alloc_ceiling_num as ACV.
    pose proof (app_facts LPA p n LO) as (PB & _ & PNS & _).   (* [comment removed for export] *)
    apply (as_shadow_visible LPA A m md a AI0).
    - unfold kLowMemEnd, kHighMemBeg. destruct PNS as [X|X]; [left; lia| right; lia].
    - replace a with (p + (a - p)) by lia. apply NO. lia.
    - right. unfold aview_of. fold (aview A m). replace a with (p + (a - p)) by lia. apply MP. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_range_ok : forall A m md p n a k,
    ainv A m md -> a_live A p = Some n -> p <= a -> a + k <= p + n -> 1 <= k ->
    range_ok (aview A m) a k.
  Proof.
    intros A m md p n a k AI0 LV Ha Hk K1.
    destruct (as_live_ok LPA A m md p n AI0 LV) as (N0 & AL & LO & HI & _).
    pose proof alloc_ceiling_num as ACV. pose proof (app_facts LPA p n LO) as (PB & _ & PNS & _).   (* [comment removed for export] *)
    split; [| split; [| split]].
    - unfold inmem_range. destruct PNS as [X|X]; [left; lia| right; lia].
    - eapply (shadow_ok_of_shpat _ p n); [exact (as_live_shadow LPA A m md p n AI0 LV)| | lia| exact Ha| exact Hk| exact K1].
      pose proof (Z.div_mod p 16 ltac:(lia)) as D. rewrite AL, Z.add_0_r in D.
      rewrite D at 1. replace (16 * (p / 16)) with ((2 * (p / 16)) * 8) by lia. apply Z.mod_mul. lia.
    - exact (live_shadow_word A m md p n a AI0 LV ltac:(lia)).
    - exact (live_shadow_word A m md p n (a + k - 1) AI0 LV ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma shadowed_range_ok : forall v a k p sz,
    bytes_at rsegs v (sh p) (shpat sz) -> p mod 8 = 0 -> 0 <= p -> p <= a -> a + k <= p + sz -> 1 <= k ->
    inmem_range a k (* [comment removed for export] *) ->
    mapped v (sh a - sh a mod 8) 8 -> mapped v (sh (a + k - 1) - sh (a + k - 1) mod 8) 8 ->
    range_ok v a k.
  Proof.
    intros v a k p sz B AL P0 Ha Hk K1 R W1 W2. split; [| split; [| split; [exact W1| exact W2]]].
    - exact R.
    - eapply shadow_ok_of_shpat; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma global_range_ok : forall v b s r a k,
    cenv v -> In (b, s, r) pa_gdescs -> b <= a -> a + k <= b + s -> 1 <= k ->
    ~ pa_static a -> ~ pa_static (a + k - 1) ->
    range_ok v a k.
  Proof.
    intros v b s r a k [CH VIS] HIn Ha Hk K1 NS1 NS2.
    pose proof (gdesc_facts b s r HIn) as (AL & SZ & _ & LO & HI).
    assert (B8 : b mod 8 = 0).
    { pose proof (Z.div_mod b 32 ltac:(lia)) as D. rewrite AL, Z.add_0_r in D. rewrite D.
      replace (32 * (b / 32)) with ((4 * (b / 32)) * 8) by lia. apply Z.mod_mul. lia. }
    split; [| split; [| split]].
    - left. lia.
    - eapply (shadow_ok_of_shpat v b s a k); [exact (global_shadow_pat v b s r CH HIn)| exact B8| lia| exact Ha| exact Hk| exact K1].
    - exact (VIS a ltac:(lia) NS1).
    - exact (VIS (a + k - 1) ltac:(lia) NS2).
  Qed.

  (* [comment removed for export] *)
  Lemma chome_range_ok : forall A m md excl p0 sz0 a k,
    ainv A m md -> chome LPA A excl p0 sz0 -> bytes_at rsegs (aview A m) (sh p0) (shpat sz0) ->
    p0 mod 8 = 0 -> 0 <= p0 -> p0 <= a -> a + k <= p0 + sz0 -> 1 <= k ->
    range_ok (aview A m) a k.
  Proof.
    intros A m md excl p0 sz0 a k AI0 HO B P8 P0 Ha Hk K1.
    pose proof alloc_ceiling_num as ACV.
    assert (G : app_range LPA p0 sz0 (* [comment removed for export] *) /\ p0 + sz0 <= alloc_ceiling /\
                forall x, a <= x < a + k -> ~ owned A x /\ aview A m (Z_to_bv 64 x) <> None).
    { destruct HO as [[LV _] | (ff & kk & age & HF & F1 & F2)].
      - destruct (as_live_ok LPA A m md p0 sz0 AI0 LV) as (N0 & AL & LO & HI & IMG & MP & NO & _).
        split; [exact LO|]. split; [exact HI|]. intros x Hx. split.
        + replace x with (p0 + (x - p0)) by lia. apply NO. lia.
        + unfold aview. replace x with (p0 + (x - p0)) by lia. apply MP. lia.
      - destruct (as_frame_ok LPA A m md ff kk age AI0 HF) as (K0 & AL & LO & HI & IMG & WR & MP & _ & _ & NO & _).
        assert (FS : 8 <= fsize kk) by (unfold fsize; pose proof (Z.pow_pos_nonneg 2 kk); nia).
        split; [eapply app_range_sub; [exact LO| lia| lia| lia]|]. split; [lia|]. intros x Hx. split.
        + replace x with (ff + (x - ff)) by lia. apply NO. lia.
        + unfold aview. replace x with (ff + (x - ff)) by lia. apply MP. lia. }
    destruct G as (LO & HI & G). pose proof (app_facts LPA p0 sz0 LO) as (PB & _ & PNS & _).
    assert (W : forall x, a <= x < a + k -> mapped (aview A m) (sh x - sh x mod 8) 8).
    { intros x Hx. destruct (G x Hx) as [NO VIS]. apply (as_shadow_visible LPA A m md x AI0).
      - unfold kLowMemEnd, kHighMemBeg. destruct PNS as [X|X]; [left; lia| right; lia].
      - exact NO.
      - right. exact VIS. }
    split; [| split; [| split]].
    - unfold inmem_range. destruct PNS as [X|X]; [left; lia| right; lia].
    - eapply shadow_ok_of_shpat; eauto.
    - exact (W a ltac:(lia)).
    - exact (W (a + k - 1) ltac:(lia)).
  Qed.
End Ranges.

(* [comment removed for export] *)
Section CEIL6.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma range_ok_high_munch : forall W (m m' : mem) a k,
  range_ok m a k -> munch W m m' -> 0 <= a -> 1 <= k -> a + k <= alloc_ceiling ->
  Forall (fun iv => SHMAX + 24 <= fst iv \/ snd iv <= 2147450880) W -> range_ok m' a k.
Proof.
  intros W m m' a k (IM & SO & W1 & W2) MU A0 K1 CE FW.
  pose proof alloc_ceiling_num as ACV.
  assert (OUT : forall x, 2147450880 <= x <= SHMAX + 16 -> outside W x).
  { intros x Hx. clear - FW Hx; try pose proof alloc_ceiling_val. induction W as [|[lo hi] W IH]; [exact I|].
    cbn. apply Forall_cons_iff in FW as [F1 FW]. split; [cbn in F1; lia| exact (IH FW)]. }
  assert (DJ : forall x n, 2147450880 <= x -> x + n <= SHMAX + 17 -> disjoint_from W x n).
  { intros x n Hx0 Hx. clear - FW Hx0 Hx; try pose proof alloc_ceiling_val. induction W as [|[lo hi] W IH]; [exact I|].
    cbn. apply Forall_cons_iff in FW as [F1 FW]. split; [cbn in F1; lia| exact (IH FW)]. }
  assert (TOP : (a + k - 1) / 8 + shadow_off <= SHMAX).
  { unfold shadow_off, SHMAX. assert ((a + k - 1) / 8 <= (140737479966720 - 1) / 8) by (apply Z.div_le_mono; lia).   (* [comment removed for export] *)
    change ((140737479966720 - 1) / 8) with 17592184995839 in *. lia. }
  assert (MONO : a / 8 <= (a + k - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (A8 : 0 <= a / 8) by (apply Z.div_pos; lia).
  unfold SHMAX, shadow_off in *.
  split; [exact IM|]. split; [| split].
  - destruct SO as (ng & lastb & E & B & L). exists ng, lastb. split; [exact E|]. split; [| exact L].
    eapply bytes_at_transport; [exact B| exact MU|].
    rewrite length_app, zeros_length. cbn [length]. apply DJ; unfold shadow_off; lia.
  - pose proof (Z.mod_pos_bound (a / 8 + 2147450880) 8 ltac:(lia)) as MB.
    assert (ML : (a / 8 + 2147450880) mod 8 <= a / 8).
    { replace (a / 8 + 2147450880) with (a / 8 + 268431360 * 8) by lia. rewrite Z_mod_plus_full. apply Z.mod_le; lia. }
    eapply mapped_munch; [exact MU| | | | exact W1]; unfold sha, mapped8, shadow_off in *;
      first [lia | intros i Hi; apply OUT; lia].
  - pose proof (Z.mod_pos_bound ((a + k - 1) / 8 + 2147450880) 8 ltac:(lia)) as MB.
    assert (ML : ((a + k - 1) / 8 + 2147450880) mod 8 <= (a + k - 1) / 8).
    { replace ((a + k - 1) / 8 + 2147450880) with ((a + k - 1) / 8 + 268431360 * 8) by lia. rewrite Z_mod_plus_full. apply Z.mod_le; lia. }
    eapply mapped_munch; [exact MU| | | | exact W2]; unfold sha, mapped8, shadow_off in *;
      first [lia | intros i Hi; apply OUT; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vct_bytes_atA : forall m, mem_inv rsegs m -> bytes_at rsegs m VCT_TYPTABA vct_bytes.
Proof.
  intros m MI. apply (ro_bytes_at rsegs m VCT_TYPTABA vct_bytes MI); [unfold VCT_TYPTABA; lia| |].
  - change (Z.of_nat (length vct_bytes)) with 512. unfold VCT_TYPTABA; lia.
  - apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma vct_readA : forall m c a, mem_inv rsegs m -> 0 <= c < 256 -> a = wa (VCT_TYPTABA + 2 * c) ->
  ov_read_bytes rsegs m a 2 = Some (le2 (Z_to_bv 64 (vct c))).
Proof.
  intros m c a MI Hc ->.
  rewrite (bytes_at_read rsegs m VCT_TYPTABA vct_bytes (2 * c) 2 (vct_bytes_atA m MI)); [| lia |].
  - f_equal. apply vct_entry. exact Hc.
  - change (length vct_bytes) with 512%nat. lia.
Qed.

(* [comment removed for export] *)
Lemma vct_shadowA : forall v, consts_hold LPA v -> bytes_at rsegs v (sh VCT_TYPTABA) (repeat (Z_to_bv 8 0) 64).
Proof.
  intros v CH. pose proof (global_shadow_pat v 0x243c0 512 640 CH ltac:(gdesc_in)) as X.
  change (shpat 512) with (repeat (Z_to_bv 8 0) 64) in X. exact X.
Qed.

(* [comment removed for export] *)

End CEIL6.
