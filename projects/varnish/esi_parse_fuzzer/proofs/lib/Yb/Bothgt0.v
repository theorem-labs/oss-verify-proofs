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
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanxvb AsanAcct AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Bothny9 AsanInit Star5ef Starr0h Stargqr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanxvb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothny9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Star5ef OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starr0h OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Stargqr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Boots35.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module Bothcs6.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec AsanAcct Asanhz7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bothny9.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanhz7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothny9.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asan672.
From Stdlib Require Uint63.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

Definition byte_zero (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.

Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_zero s base
      else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
  end.

Lemma zscanN_sound : forall s fuel base n,
  zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_zero in H.
      destruct (hex_byte_at s base) as [b|]; [|discriminate]. apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H. reflexivity.
    + apply andb_prop in H as [H1 H2]. rewrite N.div2_div in *. set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)). replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

(* [comment removed for export] *)
Lemma seg_rom_rw3 : forall a, 0xaa000 <= a < 0x60a000 ->
  seg_rom BSEGS (Z_to_bv 64 a) = hex_byte_at AsanUbsan_seg_bytes_003 (Z.to_N (a - 0xaa000)).
Proof.
  intros a Ha. unfold seg_rom, memory_read.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
  destruct (find_segment BSEGS a (Z.of_N 1)) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht). rewrite both_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size AsanUbsan_segment_000 AsanUbsan_segment_001
           AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht; try (exfalso; cbn in Hb, Ht; lia).
    match goal with |- context [seg_readable ?sg] => replace (seg_readable sg) with true by reflexivity end.
    cbn [seg_base seg_bytes AsanUbsan_segment_003]. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at].
    rewrite both_len3. replace (Z.to_N (a - Z.of_N 696320) <? 5636096)%N with true by (symmetry; apply N.ltb_lt; cbn in Hb, Ht; lia).
    change (Z.of_N 696320) with 0xaa000.
    destruct (hex_byte_at AsanUbsan_seg_bytes_003 (Z.to_N (a - 0xaa000))); reflexivity.
  - exfalso. apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003); [rewrite both_segs_eq; cbn; tauto | cbn; lia].
Qed.

Lemma rw_zero_range : forall lo n, 0xaa000 <= lo -> lo + Z.of_N n <= 0x60a000 ->
  zscanN AsanUbsan_seg_bytes_003 64 (Z.to_N (lo - 0xaa000)) n = true ->
  forall a, lo <= a < lo + Z.of_N n -> seg_rom BSEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof.
  intros lo n Hlo Hhi Hs a Ha. rewrite seg_rom_rw3 by lia.
  pose proof (zscanN_sound _ _ _ _ Hs (Z.to_N (a - lo)) ltac:(lia)) as X.
  replace (Z.to_N (lo - 0xaa000) + Z.to_N (a - lo))%N with (Z.to_N (a - 0xaa000)) in X by lia. exact X.
Qed.


(* [comment removed for export] *)
Lemma zscanN_complete : forall s f base n,
  (n <= 2 ^ N.of_nat f)%N ->
  (forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0)) ->
  zscanN s (S f) base n = true.
Proof.
  intros s f. induction f as [|f IH]; intros base n Hn H.
  - cbn [zscanN]. change (2 ^ N.of_nat 0)%N with 1%N in Hn.
    destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
    destruct (N.eqb_spec n 1) as [E1|N1]; [|lia].
    unfold byte_zero. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. rewrite H. reflexivity.
  - assert (P2 : (2 ^ N.of_nat (S f) = 2 * 2 ^ N.of_nat f)%N) by (rewrite Nat2N.inj_succ, N.pow_succ_r'; reflexivity).
    remember (S f) as f1 eqn:Ef1. cbn [zscanN].
    destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
    destruct (N.eqb_spec n 1) as [E1|N1].
    + unfold byte_zero. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. rewrite H. reflexivity.
    + rewrite N.div2_div. set (h := (n / 2)%N).
      assert (Hh : (2 * h <= n < 2 * h + 2)%N).
      { unfold h. pose proof (N.div_mod n 2 ltac:(lia)) as D. pose proof (N.mod_lt n 2 ltac:(lia)). lia. }
      subst f1. apply andb_true_intro. split.
      * apply IH; [lia|]. intros i Hi. apply H. lia.
      * apply IH; [lia|]. intros i Hi. replace (base + h + i)%N with (base + (h + i))%N by lia. apply H. lia.
Qed.

Lemma zwin_rw3 : Asan672.zwin AsanUbsan_seg_bytes_003 (Uint63.of_Z 65536) (Uint63.of_Z 11206656) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma zr_window : forall base n, (32768 <=? base)%N = true -> (base + n <=? 5636096)%N = true ->
  zscanN AsanUbsan_seg_bytes_003 64 base n = true.
Proof.
  intros base n H1 H2. apply N.leb_le in H1. apply N.leb_le in H2.
  apply (zscanN_complete _ 63).
  - change (2 ^ N.of_nat 63)%N with 9223372036854775808%N. lia.
  - intros i Hi.
    apply (Asan672.zwin_hex_byte_at _ (Uint63.of_Z 65536) (Uint63.of_Z 11206656) (base + i)%N zwin_rw3).
    + vm_compute. discriminate.
    + change (Uint63.to_Z (Uint63.of_Z 65536)) with 65536. lia.
    + change (Uint63.to_Z (Uint63.of_Z 65536)) with 65536. change (Uint63.to_Z (Uint63.of_Z 11206656)) with 11206656. lia.
Qed.

(* [comment removed for export] *)
Lemma zr_depot_tab : zscanN AsanUbsan_seg_bytes_003 64 (Z.to_N (0x196a98 - 0xaa000)) 0x400000 = true.
Proof. apply zr_window; vm_compute; congruence. Qed.
Lemma zr_depot_map1 : zscanN AsanUbsan_seg_bytes_003 64 (Z.to_N (0x596aa8 - 0xaa000)) 0x40000 = true.
Proof. apply zr_window; vm_compute; congruence. Qed.
Lemma zr_ia_inst : zscanN AsanUbsan_seg_bytes_003 64 (Z.to_N (0xb5dc0 - 0xaa000)) 0x81040 = true.
Proof. apply zr_window; vm_compute; congruence. Qed.
Lemma zr_hooks : zscanN AsanUbsan_seg_bytes_003 64 (Z.to_N (0x146680 - 0xaa000)) 80 = true.
Proof. apply zr_window; vm_compute; congruence. Qed.
Lemma zr_instance : zscanN AsanUbsan_seg_bytes_003 64 (Z.to_N (0xb1558 - 0xaa000)) 3632 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma img0_depot_tab : forall a, 0x196a98 <= a < 0x196a98 + 0x400000 -> seg_rom BSEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof. intros a Ha. apply (rw_zero_range 0x196a98 0x400000%N); [lia|cbn; lia| exact zr_depot_tab| cbn; lia]. Qed.
Lemma img0_depot_map1 : forall a, 0x596aa8 <= a < 0x596aa8 + 0x40000 -> seg_rom BSEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof. intros a Ha. apply (rw_zero_range 0x596aa8 0x40000%N); [lia|cbn; lia| exact zr_depot_map1| cbn; lia]. Qed.
Lemma img0_ia_inst : forall a, 0xb5dc0 <= a < 0xb5dc0 + 0x81040 -> seg_rom BSEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof. intros a Ha. apply (rw_zero_range 0xb5dc0 0x81040%N); [lia|cbn; lia| exact zr_ia_inst| cbn; lia]. Qed.
Lemma img0_hooks : forall a, 0x146680 <= a < 0x146680 + 80 -> seg_rom BSEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof. intros a Ha. apply (rw_zero_range 0x146680 80%N); [lia|cbn; lia| exact zr_hooks| cbn; lia]. Qed.
Lemma img0_instance : forall a, 0xb1558 <= a < 0xb1558 + 3632 -> seg_rom BSEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof. intros a Ha. apply (rw_zero_range 0xb1558 3632%N); [lia|cbn; lia| exact zr_instance| cbn; lia]. Qed.
End Bothcs6.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Fixpoint nfog (ms : list amap) : nat :=
  match ms with [] => O | m :: ms' => if is_fog m then S (nfog ms') else nfog ms' end.

(* [comment removed for export] *)
Lemma maps_match_fog : forall E ms l, maps_match E ms l ->
  exists fog : list (word * word),
    (length fog <= nfog ms)%nat /\
    (forall e, In e fog -> In e l) /\
    Forall (fun e => exists m, In m ms /\ is_fog m = true /\ bv_unsigned (snd e) <= uE E (am_len m)) fog /\
    (forall e, In e l -> (exists m, In m ms /\ is_fog m = false /\ e = amap_den E m) \/ In e fog).
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l HM.
  - cbn in HM. subst l. exists []. cbn. split; [apply le_n|]. split; [intros e []|]. split; [constructor| intros e []].
  - cbn [maps_match] in HM.
    cbn [nfog].
    destruct (is_fog m) eqn:F.
    + destruct HM as [HM | (iv & l' & -> & SZ & HM)].
      * (first [ pose proof ((IH l HM)) as dR_1; dex1 dR_1 as fog; dand4 dR_1 as L1 L2 L3 L4 | pose proof ((IH l HM)) as dR_1; dand5 dR_1 as fog L1 L2 L3 L4 | destruct (IH l HM) as (fog & L1 & L2 & L3 & L4) ]). exists fog.
        split; [lia|]. split; [exact L2|]. split.
        -- apply Forall_forall. intros e He. (first [ pose proof ((proj1 (Forall_forall _ _) L3 e He)) as dR_2; dex1 dR_2 as m'; dand3 dR_2 as A B C | pose proof ((proj1 (Forall_forall _ _) L3 e He)) as dR_2; dand4 dR_2 as m' A B C | destruct (proj1 (Forall_forall _ _) L3 e He) as (m' & A & B & C) ]). exists m'. split; [right; exact A| split; [exact B| exact C]].
        -- intros e He. destruct (L4 e He) as [(m' & A & B & C)|X]; [left; exists m'; split; [right; exact A| split; [exact B| exact C]]| right; exact X].
      * (first [ pose proof ((IH l' HM)) as dR_3; dex1 dR_3 as fog; dand4 dR_3 as L1 L2 L3 L4 | pose proof ((IH l' HM)) as dR_3; dand5 dR_3 as fog L1 L2 L3 L4 | destruct (IH l' HM) as (fog & L1 & L2 & L3 & L4) ]). exists (iv :: fog).
        split; [cbn [length]; lia|]. split; [intros e [<-|He]; [left; reflexivity| right; exact (L2 e He)]|]. split.
        -- constructor.
           ++ exists m. split; [left; reflexivity|]. split; [exact F| exact SZ].
           ++ apply Forall_forall. intros e He. (first [ pose proof ((proj1 (Forall_forall _ _) L3 e He)) as dR_4; dex1 dR_4 as m'; dand3 dR_4 as A B C | pose proof ((proj1 (Forall_forall _ _) L3 e He)) as dR_4; dand4 dR_4 as m' A B C | destruct (proj1 (Forall_forall _ _) L3 e He) as (m' & A & B & C) ]). exists m'. split; [right; exact A| split; [exact B| exact C]].
        -- intros e [<-|He]; [right; left; reflexivity|].
           destruct (L4 e He) as [(m' & A & B & C)|X]; [left; exists m'; split; [right; exact A| split; [exact B| exact C]]| right; right; exact X].
    + (first [ dex1 HM as l'; destruct HM as [-> HM] | dand3 HM as l' -> HM | destruct HM as (l' & -> & HM) ]).
      (first [ pose proof ((IH l' HM)) as dR_6; dex1 dR_6 as fog; dand4 dR_6 as L1 L2 L3 L4 | pose proof ((IH l' HM)) as dR_6; dand5 dR_6 as fog L1 L2 L3 L4 | destruct (IH l' HM) as (fog & L1 & L2 & L3 & L4) ]). exists fog.
      split; [exact L1|]. split; [intros e He; right; exact (L2 e He)|]. split.
      * apply Forall_forall. intros e He. (first [ pose proof ((proj1 (Forall_forall _ _) L3 e He)) as dR_7; dex1 dR_7 as m'; dand3 dR_7 as A B C | pose proof ((proj1 (Forall_forall _ _) L3 e He)) as dR_7; dand4 dR_7 as m' A B C | destruct (proj1 (Forall_forall _ _) L3 e He) as (m' & A & B & C) ]). exists m'. split; [right; exact A| split; [exact B| exact C]].
      * intros e [<-|He]; [left; exists m; split; [left; reflexivity| split; [exact F| reflexivity]]|].
        destruct (L4 e He) as [(m' & A & B & C)|X]; [left; exists m'; split; [right; exact A| split; [exact B| exact C]]| right; exact X].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Extract.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV := (SINV0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 BPH sp rdraw argv envp uid hw).
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  #[local] Notation LIM := (@AsanInit.blim BL).

  Variable cs : acs.
  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis CS : cs_ok BSEGS BOTH LIM SINV argH fs E cs R FULL model.

  #[local] Notation MR := (Mr BOTH argH E cs model FULL).

  (* [comment removed for export] *)
  Definition khas (K : kentry) : bool := existsb (kentry_eqb K) (kn cs).

  Lemma khas_ok : forall K, khas K = true -> kentry_ok BSEGS E MR K.
  Proof.
    intros K H. unfold khas in H. apply existsb_exists in H as [k [Hin Heq]]. apply kentry_eqb_eq in Heq. subst k.
    exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ CS) _ Hin).
  Qed.

  (* [comment removed for export] *)
  Lemma pre_top : alloc_top (m_vmmaps model) + 8388608 = bv_unsigned sp.
  Proof.
    rewrite (co_top _ _ _ _ _ _ _ _ _ _ _ CS).
    exact (SINV0_sp BPH sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit (SINV0 BPH sp rdraw brk0 argv envp uid hw) (fun E M H => H)
             E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ CS)).
  Qed.
  Lemma pre_top_ceil : CEIL <= alloc_top (m_vmmaps model).
  Proof. pose proof pre_top. pose proof Hsp as (H1 & _). unfold sp_window_lo in H1. unfold CEIL. lia. Qed.

  (* [comment removed for export] *)
  Lemma Mr_some : forall a b, MR a = Some b -> FULL a = Some b.
  Proof. intros a b H. unfold Mr, mrestrict in H. destruct (hid BOTH argH E cs model a); [discriminate|exact H]. Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma hid_image : forall a : word, img_lo BOTH <= bv_unsigned a < img_hi BOTH -> hid BOTH argH E cs model a = false.
  Proof.
    intros a Ha. unfold hid. destruct (argH0 BPH sp rdraw argv envp uid hw E a) eqn:HA.
    - exfalso. pose proof (argH0_high BPH sp rdraw argv envp uid hw Hsp Hva E a HA) as X. unfold CEIL in X. cbn [img_hi BOTH] in Ha. lia.
    - cbn [orb]. unfold vis. unfold in_hull. destruct Ha as [H1 H2].
      rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2). reflexivity.
  Qed.
  Lemma Mr_image : forall a : word, img_lo BOTH <= bv_unsigned a < img_hi BOTH -> MR a = FULL a.
  Proof. intros a Ha. unfold Mr, mrestrict. rewrite (hid_image a Ha). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rdn_ext : forall (m1 m2 : word -> option byte) n (a : word),
    (forall j, (j < n)%nat -> m1 (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = m2 (Z_to_bv 64 (bv_unsigned a + Z.of_nat j))) ->
    rdn BSEGS m1 a n = rdn BSEGS m2 a n.
  Proof.
    intros m1 m2 n. induction n as [|n IH]; intros a Heq; [reflexivity|].
    cbn [rdn]. pose proof (Heq 0%nat ltac:(lia)) as H0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
    rewrite (IH (a + 1)%bv); [reflexivity|].
    intros j Hj. rewrite !u_succ_shift. replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia. apply Heq. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_bytes : forall (m : word -> option byte) n (a : word) bs,
    (forall j, (j < n)%nat -> seg_rom BSEGS (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = None) ->
    rdn BSEGS m a n = Some bs ->
    forall j, (j < n)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
  Proof.
    intros m n. induction n as [|n IH]; intros a bs Hrom Hr j Hj; [lia|].
    cbn [rdn] in Hr. pose proof (Hrom 0%nat ltac:(lia)) as R0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in R0.
    destruct (m a) as [b|] eqn:Hm.
    - destruct (rdn BSEGS m (a + 1)%bv n) as [rest|] eqn:Hr'; [|discriminate]. injection Hr as <-.
      destruct j as [|j].
      + rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned. exact Hm.
      + cbn [nth]. specialize (IH (a + 1)%bv rest).
        rewrite <- (u_succ_shift a (Z.of_nat j)) in IH |- * || idtac.
        replace (bv_unsigned a + Z.of_nat (S j)) with (bv_unsigned a + (1 + Z.of_nat j)) by lia. rewrite <- u_succ_shift.
        apply IH; [|exact Hr'|lia]. intros k Hk. rewrite u_succ_shift. replace (1 + Z.of_nat k) with (Z.of_nat (S k)) by lia. apply Hrom. lia.
    - rewrite R0 in Hr. discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma store_ok_present : forall (m : word -> option byte) n (a : word),
    store_ok BSEGS m a n = true -> bv_unsigned a + Z.of_nat n <= 2^64 ->
    forall j, (j < n)%nat -> find_segment BSEGS (bv_unsigned a + Z.of_nat j) 1 = None -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None.
  Proof.
    intros m n. induction n as [|n IH]; intros a H Hn j Hj Hseg; [lia|].
    cbn [store_ok] in H. destruct (wview BSEGS m a) as [b|] eqn:Ew; [|discriminate].
    destruct j as [|j].
    - rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in *. unfold wview in Ew. rewrite Hseg in Ew.
      destruct (m a); [discriminate|discriminate].
    - pose proof (u64_range a) as Ra.
      assert (E1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      replace (bv_unsigned a + Z.of_nat (S j)) with (bv_unsigned (a + 1)%bv + Z.of_nat j) in * by lia.
      apply (IH (a + 1)%bv H ltac:(lia) j ltac:(lia) Hseg).
  Qed.

  (* [comment removed for export] *)
  Section AtBase.
    Variable b : expr.
    Variable B : Z.
    Hypothesis Ub : bv_unsigned (edenot E b) = B.

    Lemma estart_at : forall off, estart E (SA b off) = B + off.
    Proof. intros off. unfold estart. cbn [a_base a_off]. rewrite Ub. reflexivity. Qed.
    Lemma elenZ_lit : forall n, 0 <= n < 2^64 -> elenZ E (ELit n) = n.
    Proof. intros n Hn. unfold elenZ. cbn [edenot]. rewrite u_lit64a. apply Z.mod_small. lia. Qed.
    Lemma adenot_at : forall off, 0 <= B + off < 2^64 -> adenot E (SA b off) = Z_to_bv 64 (B + off).
    Proof.
      intros off Hr. unfold adenot. cbn [a_base a_off]. unfold v_addi. rewrite Ub. reflexivity.
    Qed.

    Lemma pre_zero_at : forall off n, khas (KZero (SA b off) (ELit n)) = true -> 0 <= n < 2^64 ->
      forall i, 0 <= i < n -> FULL (Z_to_bv 64 (B + off + i)) = Some (Z_to_bv 8 0).
    Proof.
      intros off n H Hn i Hi. apply khas_ok in H. destruct H as [_ H].
      rewrite estart_at, elenZ_lit in H by lia. apply Mr_some. apply H. exact Hi.
    Qed.

    Lemma pre_fill_at : forall off n c, khas (KFill (SA b off) (ELit n) c) = true -> 0 <= n < 2^64 ->
      forall i, 0 <= i < n -> FULL (Z_to_bv 64 (B + off + i)) = Some (Z_to_bv 8 c).
    Proof.
      intros off n c H Hn i Hi. apply khas_ok in H. destruct H as [_ H].
      rewrite estart_at, elenZ_lit in H by lia. apply Mr_some. apply H. exact Hi.
    Qed.

    (* [comment removed for export] *)
    Lemma pre_word_at : forall off w ve, khas (KWord (SA b off) w ve) = true ->
      0 <= B + off -> B + off + Z.of_nat w <= 2^64 ->
      (forall j, (j < w)%nat -> seg_rom BSEGS (Z_to_bv 64 (B + off + Z.of_nat j)) = None) ->
      forall j, (j < w)%nat -> FULL (Z_to_bv 64 (B + off + Z.of_nat j)) = Some (nth j (word_to_le_bytes w (edenot E ve)) (Z_to_bv 8 0)).
    Proof.
      intros off w ve H Hlo Hhi Hrom j Hj. apply khas_ok in H. (first [ dand3 H as Hw _ Hr | destruct H as (Hw & _ & Hr) ]).
      rewrite adenot_at in Hr by lia. apply Mr_some.
      pose proof (rdn_bytes MR w (Z_to_bv 64 (B + off)) _ ltac:(intros k Hk; rewrite u_lit64a, Z.mod_small by lia; apply Hrom; exact Hk) Hr j Hj) as X.
      rewrite u_lit64a, Z.mod_small in X by lia. exact X.
    Qed.

    (* [comment removed for export] *)
    Lemma pre_word_img_at : forall off w ve, khas (KWord (SA b off) w ve) = true ->
      img_lo BOTH <= B + off -> B + off + Z.of_nat w <= img_hi BOTH ->
      rdn BSEGS FULL (Z_to_bv 64 (B + off)) w = Some (word_to_le_bytes w (edenot E ve)).
    Proof.
      intros off w ve H Hlo Hhi. apply khas_ok in H. (first [ dand3 H as Hw _ Hr | destruct H as (Hw & _ & Hr) ]).
      cbn [img_lo img_hi BOTH] in Hlo, Hhi.
      rewrite adenot_at in Hr by lia.
      rewrite <- (rdn_ext MR FULL w (Z_to_bv 64 (B + off))); [exact Hr|].
      intros j Hj. apply Mr_image. cbn [img_lo img_hi BOTH]. rewrite (u_lit64a (B + off)), (Z.mod_small (B + off)) by lia.
      rewrite u_lit64a, Z.mod_small by lia. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma pre_wr_at : forall off n, khas (KWr (SA b off) (ELit n)) = true ->
      0 <= B + off -> 0 <= n < 2^64 -> B + off + n <= 2^64 ->
      (forall i, 0 <= i < n -> find_segment BSEGS (B + off + i) 1 = None) ->
      forall i, 0 <= i < n -> FULL (Z_to_bv 64 (B + off + i)) <> None.
    Proof.
      intros off n H Hlo Hn Hhi Hseg i Hi. apply khas_ok in H. destruct H as [_ H].
      rewrite estart_at, elenZ_lit in H by lia.
      specialize (H i 1%nat ltac:(lia) ltac:(lia)).
      intros X. apply (store_ok_present MR 1 (Z_to_bv 64 (B + off + i)) H ltac:(rewrite u_lit64a, Z.mod_small; lia) 0%nat ltac:(lia)).
      - rewrite u_lit64a, Z.mod_small by lia. rewrite Z.add_0_r. apply Hseg. lia.
      - rewrite u_lit64a, Z.mod_small, Nat2Z.inj_0, Z.add_0_r by lia.
        unfold Mr, mrestrict. destruct (hid BOTH argH E cs model (Z_to_bv 64 (B + off + i))); [reflexivity|exact X].
    Qed.
  End AtBase.

  (* [comment removed for export] *)
  Lemma ub_lit : bv_unsigned (edenot E (ELit 0)) = 0.
  Proof. cbn [edenot]. rewrite u_lit64a. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma ub_scale : forall c v lo hi, khas (KRange (EVar v) lo hi) = true -> 0 < c <= 4096 -> 0 <= lo -> 4096 * hi < 2^64 ->
    bv_unsigned (edenot E (EMd Instr.M_MUL (ELit c) (EVar v))) = c * bv_unsigned (ev E v).
  Proof.
    intros c v lo hi H Hc Hlo Hhi. apply khas_ok in H. cbn [kentry_ok edenot] in H. cbn [edenot].
    cbn [mul_div]. rewrite bv_mul_unsigned, u_lit64a. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    pose proof (u64_range (ev E v)). rewrite (Z.mod_small c) by lia. apply Z.mod_small. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma pre_range : forall v lo hi, khas (KRange (EVar v) lo hi) = true -> lo <= bv_unsigned (ev E v) <= hi.
  Proof. intros v lo hi H. apply khas_ok in H. cbn [kentry_ok edenot] in H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma pre_halted : m_halted model = None.
  Proof. exact (co_halt _ _ _ _ _ _ _ _ _ _ _ CS). Qed.
  Lemma pre_fs : m_fs model = fs.
  Proof. exact (co_fs _ _ _ _ _ _ _ _ _ _ _ CS). Qed.
  Lemma pre_fds_std : a_fd cs = FdStd -> m_fds model = fds_std.
  Proof. intros H. pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ CS) as X. rewrite H in X. exact X. Qed.

  (* [comment removed for export] *)
  Lemma pre_sinv : SINV E FULL.
  Proof. exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ CS). Qed.

  Lemma pre_ev_lt9 : forall n, (n < NX0)%nat -> ev E n = ev (E0 BPH sp rdraw brk0 argv envp uid hw) n.
  Proof. intros n Hn. destruct pre_sinv as [H _]. apply H. exact Hn. Qed.

  Lemma pre_v0 : bv_unsigned (ev E 0%nat) = bv_unsigned sp / 32768.
  Proof.
    rewrite (pre_ev_lt9 0%nat) by (unfold NX0; lia). unfold E0. cbn [ev vals0 nth].
    pose proof (u64_range sp). rewrite u_lit64a. apply Z.mod_small.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Lemma pre_v6 : bv_unsigned (ev E 6%nat) = (bv_unsigned sp mod 32768) / 16.
  Proof.
    rewrite (pre_ev_lt9 6%nat) by (unfold NX0; lia). unfold E0. cbn [ev vals0 nth].
    pose proof (u64_range sp). rewrite u_lit64a. apply Z.mod_small.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Lemma pre_v1 : bv_unsigned (ev E 1%nat) = Z.of_nat (length argv).
  Proof.
    rewrite (pre_ev_lt9 1%nat) by (unfold NX0; lia). unfold E0. cbn [ev vals0 nth].
    pose proof (valid_argv_len argv Hva). rewrite u_lit64a. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pre_sp0 : 32768 * bv_unsigned (ev E 0%nat) + 16 * bv_unsigned (ev E 6%nat) = bv_unsigned sp.
  Proof.
    rewrite pre_v0, pre_v6. destruct Hsp as (_ & _ & Hal).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma pre_reg : forall r : bv 5, getr R r = edenot E (sr_get (s_regs (a_ss cs)) r).
  Proof. exact (co_regs _ _ _ _ _ _ _ _ _ _ _ CS). Qed.

  (* [comment removed for export] *)
  Lemma pre_argblock : forall a, argH0 BPH sp rdraw argv envp uid hw E a = true -> FULL a = wrap_mem BPH sp argv envp uid hw rdraw a.
  Proof. destruct pre_sinv as [_ H]. exact H. Qed.

  (* [comment removed for export] *)
  Lemma pre_in_maps : forall m, In m (a_maps cs) -> is_fog m = false ->
    In (amap_den E m) (vm_maps (m_vmmaps model)).
  Proof. intros m Hin Hf. exact (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ CS) Hin Hf). Qed.

  Lemma pre_limit : vm_limit (m_vmmaps model) = LIM.
  Proof. exact (co_limit _ _ _ _ _ _ _ _ _ _ _ CS). Qed.
  (* [comment removed for export] *)
  Lemma pre_res : vm_reserved (m_vmmaps model) = segments_reserved BSEGS.
  Proof. exact (co_res _ _ _ _ _ _ _ _ _ _ _ CS). Qed.
  Lemma pre_vmmaps : exists fog : list (word * word),
    (length fog <= nfog (a_maps cs))%nat /\
    (forall e, In e fog -> In e (vm_maps (m_vmmaps model))) /\
    Forall (fun e => exists m, In m (a_maps cs) /\ is_fog m = true /\ 0 < bv_unsigned (snd e) <= uE E (am_len m)) fog /\
    (forall e, In e (vm_maps (m_vmmaps model)) -> (exists m, In m (a_maps cs) /\ is_fog m = false /\ e = amap_den E m) \/ In e fog).
  Proof.
    (first [ pose proof ((maps_match_fog E _ _ (co_maps _ _ _ _ _ _ _ _ _ _ _ CS))) as dR_10; dex1 dR_10 as fog; dand4 dR_10 as L1 L2 L3 L4 | pose proof ((maps_match_fog E _ _ (co_maps _ _ _ _ _ _ _ _ _ _ _ CS))) as dR_10; dand5 dR_10 as fog L1 L2 L3 L4 | destruct (maps_match_fog E _ _ (co_maps _ _ _ _ _ _ _ _ _ _ _ CS)) as (fog & L1 & L2 & L3 & L4) ]).
    exists fog. split; [exact L1|]. split; [exact L2|]. split; [| exact L4].
    apply Forall_forall. intros e He. (first [ pose proof ((proj1 (Forall_forall _ _) L3 e He)) as dR_11; dex1 dR_11 as m; dand3 dR_11 as A B C | pose proof ((proj1 (Forall_forall _ _) L3 e He)) as dR_11; dand4 dR_11 as m A B C | destruct (proj1 (Forall_forall _ _) L3 e He) as (m & A & B & C) ]).
    exists m. split; [exact A|]. split; [exact B|]. split; [| exact C].
    exact (proj1 (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ CS) e (L2 e He))).
  Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma pre_hidden_zero : forall (mz : amap) (z : Z),
    In mz (a_maps cs) -> is_fog mz = false -> am_kind mz = KRWLAZY ->
    uE E (am_base mz) <= z < uE E (am_base mz) + uE E (am_len mz) ->
    z < CEIL -> img_hi BOTH <= z ->
    in_vis E cs z = false -> in_sh BOTH E cs z = false -> in_ghost E cs z = false ->
    FULL (Z_to_bv 64 z) = Some (Z_to_bv 8 0).
  Proof.
    intros mz z Hmin Hnf Hkind Hz Hceil Himg Hnv Hns Hng.
    pose proof (u64_range (edenot E (am_base mz))) as Rb.
    assert (Rz : 0 <= z < 2^64) by (unfold uE in Hz; unfold CEIL in Hceil; lia).
    set (a := Z_to_bv 64 z). assert (Ua : bv_unsigned a = z) by (unfold a; rewrite u_lit64a; apply Z.mod_small; exact Rz).
    assert (Hm1 : in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true).
    { eapply in_ivs_maps_match; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ CS) | exact Hmin | exact Hnf |]. rewrite Ua. unfold uE in Hz. exact Hz. }
    destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ CS) mz Hmin Hkind a ltac:(rewrite Ua; unfold uE in Hz; exact Hz)) as [Hna Hlz].
    assert (Hargh : argH0 BPH sp rdraw argv envp uid hw E a = false).
    { destruct (argH0 BPH sp rdraw argv envp uid hw E a) eqn:Ha; [|reflexivity]. pose proof (argH0_high BPH sp rdraw argv envp uid hw Hsp Hva E a Ha). lia. }
    assert (Hhid : hid BOTH (argH0 BPH sp rdraw argv envp uid hw) E cs model a = true).
    { unfold hid. rewrite Hargh. cbn [orb]. apply negb_true_iff. unfold vis.
      rewrite Hm1, Hna, Hlz. cbn [negb andb]. unfold in_allow. rewrite Ua, Hnv, Hns. cbn [orb].
      unfold in_hull. replace (z <? img_hi BOTH) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
      pose proof pre_top_ceil. replace (alloc_top (m_vmmaps model) <=? z) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    rewrite <- Ua in Hng. exact (co_zero _ _ _ _ _ _ _ _ _ _ _ CS a Hhid Hm1 Hna Hlz Hng).
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mb (a : Z) : option byte :=
    match FULL (Z_to_bv 64 a) with Some b => Some b | None => seg_rom BSEGS (Z_to_bv 64 a) end.

  (* [comment removed for export] *)
  Lemma rdn_mbytes : forall (m : word -> option byte) n (a : word) bs,
    rdn BSEGS m a n = Some bs ->
    forall j, (j < n)%nat ->
      match m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) with Some b => Some b | None => seg_rom BSEGS (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) end
      = Some (nth j bs (Z_to_bv 8 0)).
  Proof.
    intros m n. induction n as [|n IH]; intros a bs Hr j Hj; [lia|].
    cbn [rdn] in Hr.
    destruct (match m a with Some b => Some b | None => seg_rom BSEGS a end) as [b|] eqn:Hm; [|discriminate].
    destruct (rdn BSEGS m (a + 1)%bv n) as [rest|] eqn:Hr'; [|discriminate]. injection Hr as <-.
    destruct j as [|j].
    - rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned. exact Hm.
    - cbn [nth]. replace (bv_unsigned a + Z.of_nat (S j)) with (bv_unsigned a + (1 + Z.of_nat j)) by lia. rewrite <- u_succ_shift.
      apply (IH (a + 1)%bv rest Hr' j ltac:(lia)).
  Qed.

  Lemma nth_Z_to_le_bytes : forall n z i, (i < n)%nat ->
    nth i (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat i)).
  Proof.
    induction n as [|n IH]; intros z i Hi; [lia|].
    cbn [Z_to_le_bytes]. destruct i as [|i].
    - cbn [nth]. rewrite Z.shiftr_0_r. reflexivity.
    - cbn [nth]. rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Fixpoint kbyte (k : list kentry) (a : Z) : option byte :=
    match k with
    | [] => None
    | KWord (SA (ELit 0) b) w (ELit v) :: k' =>
        if ((b <=? a) && (a <? b + Z.of_nat w))%bool
        then Some (Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 v)) (8 * (a - b)))) else kbyte k' a
    | KZero (SA (ELit 0) b) (ELit n) :: k' =>
        if ((b <=? a) && (a <? b + n) && (0 <=? n) && (n <? 2^64))%bool then Some (Z_to_bv 8 0) else kbyte k' a
    | KFill (SA (ELit 0) b) (ELit n) c :: k' =>
        if ((b <=? a) && (a <? b + n) && (0 <=? n) && (n <? 2^64))%bool then Some (Z_to_bv 8 c) else kbyte k' a
    | _ :: k' => kbyte k' a
    end.

  Lemma kbyte_sound : forall k a b, Forall (kentry_ok BSEGS E MR) k -> kbyte k a = Some b -> 0 <= a < 2^64 -> mb a = Some b.
  Proof.
    intros k a b HF. induction HF as [|K k' HK HF IH]; intros H Ha; [discriminate|].
    assert (DFLT : kbyte k' a = Some b -> mb a = Some b) by (intros X; exact (IH X Ha)).
    cbn [kbyte] in H.
    destruct K as [sa w v|sa n|sa n kk|lo hi|e m0|e lo hi|sa n|a1 n1 a2 n2|sa n c|sa n]; try exact (DFLT H).
    - (* [comment removed for export] *) destruct sa as [bse off]. destruct bse as [z|vv|oa x y|ow x y|om x y|omw x y|sx lo n e|sx kk i n]; try exact (DFLT H). destruct z; try exact (DFLT H).
      destruct v as [v|vv|oa x' y'|ow x' y'|om x' y'|omw x' y'|sx lo n e|sx kk i n]; try exact (DFLT H).
      destruct ((off <=? a) && (a <? off + Z.of_nat w))%bool eqn:C; [|exact (DFLT H)]. injection H as <-.
      apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
      (first [ dand3 HK as Hw Hfl Hr | destruct HK as (Hw & Hfl & Hr) ]). unfold flat in Hfl. rewrite (estart_at (ELit 0) 0 ub_lit) in Hfl.
      rewrite (adenot_at (ELit 0) 0 ub_lit) in Hr by lia. rewrite Z.add_0_l in Hr.
      pose proof (rdn_mbytes MR w (Z_to_bv 64 off) _ Hr (Z.to_nat (a - off)) ltac:(lia)) as X.
      rewrite u_lit64a, Z.mod_small in X by lia. replace (off + Z.of_nat (Z.to_nat (a - off))) with a in X by lia.
      unfold word_to_le_bytes in X. rewrite nth_Z_to_le_bytes in X by lia. rewrite Z2Nat.id in X by lia.
      cbn [edenot] in X. unfold mb. unfold Mr, mrestrict in X.
      destruct (hid BOTH argH E cs model (Z_to_bv 64 a)) eqn:Hh.
      + (* [comment removed for export] *)
        destruct (seg_rom BSEGS (Z_to_bv 64 a)) as [rb|] eqn:Hrom; [|discriminate].
        exfalso. unfold seg_rom in Hrom. unfold memory_read in Hrom.
        destruct (find_segment BSEGS (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [seg|] eqn:Hf; [|discriminate].
        apply find_segment_some_spec in Hf as (Hin & Hb1 & Hb2).
        pose proof (proj1 (forallb_forall _ _) both_segs_in_hull seg Hin) as SB. apply andb_true_iff in SB as [SB1 SB2].
        apply Z.leb_le in SB1. apply Z.leb_le in SB2.
        rewrite (hid_image (Z_to_bv 64 a)) in Hh; [discriminate|]. lia.
      + exact X.
    - (* [comment removed for export] *) destruct sa as [bse off]. destruct bse as [z|vv|oa x y|ow x y|om x y|omw x y|sx lo n0 e|sx kk i n0]; try exact (DFLT H). destruct z; try exact (DFLT H).
      destruct n as [n|vv|oa x y|ow x y|om x y|omw x y|sx lo n0 e|sx kk i n0]; try exact (DFLT H).
      destruct ((off <=? a) && (a <? off + n) && (0 <=? n) && (n <? 2^64))%bool eqn:C; [|exact (DFLT H)]. injection H as <-.
      apply andb_true_iff in C as [C C4]. apply andb_true_iff in C as [C C3]. apply andb_true_iff in C as [C1 C2].
      apply Z.leb_le in C1. apply Z.ltb_lt in C2. apply Z.leb_le in C3. apply Z.ltb_lt in C4.
      destruct HK as [Hfl Hz]. rewrite (estart_at (ELit 0) 0 ub_lit) in Hz.
      rewrite (elenZ_lit n) in Hz by lia.
      specialize (Hz (a - off) ltac:(lia)). replace (0 + off + (a - off)) with a in Hz by lia.
      unfold mb. rewrite (Mr_some _ _ Hz). reflexivity.
    - (* [comment removed for export] *) destruct sa as [bse off]. destruct bse as [z|vv|oa x y|ow x y|om x y|omw x y|sx lo n0 e|sx kk i n0]; try exact (DFLT H). destruct z; try exact (DFLT H).
      destruct n as [n|vv|oa x y|ow x y|om x y|omw x y|sx lo n0 e|sx kk i n0]; try exact (DFLT H).
      destruct ((off <=? a) && (a <? off + n) && (0 <=? n) && (n <? 2^64))%bool eqn:C; [|exact (DFLT H)]. injection H as <-.
      apply andb_true_iff in C as [C C4]. apply andb_true_iff in C as [C C3]. apply andb_true_iff in C as [C1 C2].
      apply Z.leb_le in C1. apply Z.ltb_lt in C2. apply Z.leb_le in C3. apply Z.ltb_lt in C4.
      destruct HK as [Hfl Hz]. rewrite (estart_at (ELit 0) 0 ub_lit) in Hz.
      rewrite (elenZ_lit n) in Hz by lia.
      specialize (Hz (a - off) ltac:(lia)). replace (0 + off + (a - off)) with a in Hz by lia.
      unfold mb. rewrite (Mr_some _ _ Hz). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma kimg_mb : forall lo hi a, khas (KImg lo hi) = true -> lo <= a < hi -> img_lo BOTH <= lo -> hi <= img_hi BOTH ->
    FULL (Z_to_bv 64 a) = None /\ mb a = seg_rom BSEGS (Z_to_bv 64 a).
  Proof.
    intros lo hi a H Ha Hlo Hhi. apply khas_ok in H. (first [ dand3 H as _ _ H | destruct H as (_ & _ & H) ]). specialize (H a Ha).
    rewrite Mr_image in H by (rewrite u_lit64a, Z.mod_small; cbn [img_lo img_hi BOTH] in *; lia).
    split; [exact H|]. unfold mb. rewrite H. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition kimg_cov1 (k : list kentry) (a : Z) : bool :=
    existsb (fun K => match K with KImg lo hi => (lo <=? a) && (a <? hi) && (img_lo BOTH <=? lo) && (hi <=? img_hi BOTH) | _ => false end)%bool k.
  Definition byte_okb (k : list kentry) (a : Z) (b : byte) : bool :=
    match kbyte k a with
    | Some b' => bv_eqb b' b
    | None => kimg_cov1 k a && match seg_rom BSEGS (Z_to_bv 64 a) with Some b' => bv_eqb b' b | None => false end
    end%bool.
  Fixpoint bytes_okb (k : list kentry) (a : Z) (bs : list byte) : bool :=
    match bs with [] => true | b :: bs' => byte_okb k a b && bytes_okb k (a + 1) bs' end%bool.
  (* [comment removed for export] *)
  Definition kzero_covr (k : list kentry) (a n : Z) : bool :=
    existsb (fun K => match K with
      | KZero (SA (ELit 0) b) (ELit m) => (b <=? a) && (a + n <=? b + m) && (0 <=? m) && (m <? 2^64)
      | _ => false end)%bool k.
  Definition kimg_covr (k : list kentry) (a n : Z) : bool :=
    existsb (fun K => match K with
      | KImg lo hi => (lo <=? a) && (a + n <=? hi) && (img_lo BOTH <=? lo) && (hi <=? img_hi BOTH)
      | _ => false end)%bool k.
  Fixpoint bytes_eqb (xs ys : list byte) : bool :=
    match xs, ys with [], [] => true | x :: xs', y :: ys' => bv_eqb x y && bytes_eqb xs' ys' | _, _ => false end%bool.
  Definition cell_okb (k : list kentry) (a : Z) (bs : list byte) : bool :=
    let n := Z.of_nat (length bs) in
    if kzero_covr k a n then forallb (fun b => bv_eqb b (Z_to_bv 8 0)) bs
    else if kimg_covr k a n then
      match rdn BSEGS (fun _ => None) (Z_to_bv 64 a) (length bs) with Some bs' => bytes_eqb bs' bs | None => false end
    else bytes_okb k a bs.
  Definition cells_okb (l : list (Z * list byte)) : bool :=
    forallb (fun c => (0 <=? fst c) && (fst c + Z.of_nat (length (snd c)) <=? 2^64) && cell_okb (kn cs) (fst c) (snd c))%bool l.

  Lemma bv_eqb_eq8 : forall a b : byte, bv_eqb a b = true -> a = b.
  Proof. intros a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

  Lemma byte_okb_sound : forall a b, byte_okb (kn cs) a b = true -> 0 <= a < 2^64 -> mb a = Some b.
  Proof.
    intros a b H Ha. unfold byte_okb in H.
    destruct (kbyte (kn cs) a) as [b'|] eqn:KB.
    - apply bv_eqb_eq8 in H. subst b'. exact (kbyte_sound _ _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ CS) KB Ha).
    - apply andb_true_iff in H as [HC HR]. unfold kimg_cov1 in HC. apply existsb_exists in HC as [K [HK HB]].
      destruct K; try discriminate. apply andb_true_iff in HB as [HB H4]. apply andb_true_iff in HB as [HB H3]. apply andb_true_iff in HB as [H1 H2].
      apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
      assert (KH : khas (KImg lo hi) = true).
      { unfold khas. apply existsb_exists. exists (KImg lo hi). split; [exact HK|]. cbn. rewrite !Z.eqb_refl. reflexivity. }
      destruct (kimg_mb lo hi a KH ltac:(lia) H3 H4) as [_ E2]. rewrite E2.
      destruct (seg_rom BSEGS (Z_to_bv 64 a)) as [b'|]; [|discriminate]. apply bv_eqb_eq8 in HR. subst b'. reflexivity.
  Qed.

  Lemma bytes_okb_sound : forall bs a, bytes_okb (kn cs) a bs = true -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
    forall i, (i < length bs)%nat -> mb (a + Z.of_nat i) = nth_error bs i.
  Proof.
    induction bs as [|b bs IH]; intros a H Ha Hl i Hi; [cbn in Hi; lia|].
    cbn [bytes_okb] in H. apply andb_true_iff in H as [H1 H2]. cbn [length] in Hl.
    destruct i as [|i].
    - rewrite Nat2Z.inj_0, Z.add_0_r. cbn. apply byte_okb_sound; [exact H1| lia].
    - cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply IH; [exact H2| lia| lia| cbn in Hi; lia].
  Qed.

  Lemma bytes_eqb_eq : forall xs ys, bytes_eqb xs ys = true -> xs = ys.
  Proof.
    induction xs as [|x xs IH]; intros [|y ys] H; cbn in H; try discriminate; [reflexivity|].
    apply andb_true_iff in H as [H1 H2]. apply bv_eqb_eq8 in H1. subst y. f_equal. apply IH. exact H2.
  Qed.

  Lemma cell_okb_sound : forall a bs, cell_okb (kn cs) a bs = true -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
    forall i, (i < length bs)%nat -> mb (a + Z.of_nat i) = nth_error bs i.
  Proof.
    intros a bs H Ha Hl i Hi. unfold cell_okb in H.
    destruct (kzero_covr (kn cs) a (Z.of_nat (length bs))) eqn:KZ.
    - (* [comment removed for export] *)
      unfold kzero_covr in KZ. apply existsb_exists in KZ as [K [HK HB]].
      destruct K as [sa w v|sa n|sa n kk|lo hi|e m0|e lo hi|sa n|a1 n1 a2 n2|sa n c|sa n]; try discriminate.
      destruct sa as [bse off]. destruct bse as [z|vv|oa x y|ow x y|om x y|omw x y|sx lo n0 e|sx kk ii n0]; try discriminate. destruct z; try discriminate.
      destruct n as [n|vv|oa x y|ow x y|om x y|omw x y|sx lo n0 e|sx kk ii n0]; try discriminate.
      apply andb_true_iff in HB as [HB C4]. apply andb_true_iff in HB as [HB C3]. apply andb_true_iff in HB as [C1 C2].
      apply Z.leb_le in C1. apply Z.leb_le in C2. apply Z.leb_le in C3. apply Z.ltb_lt in C4.
      pose proof (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ CS) _ HK) as [Hfl Hz].
      rewrite (estart_at (ELit 0) 0 ub_lit) in Hz. rewrite (elenZ_lit n) in Hz by lia.
      specialize (Hz (a + Z.of_nat i - off) ltac:(lia)). replace (0 + off + (a + Z.of_nat i - off)) with (a + Z.of_nat i) in Hz by lia.
      unfold mb. rewrite (Mr_some _ _ Hz). symmetry.
      pose proof (proj1 (forallb_forall _ _) H) as HBs.
      destruct (nth_error bs i) as [b|] eqn:NB; [| apply nth_error_None in NB; lia].
      specialize (HBs b (nth_error_In _ _ NB)). apply bv_eqb_eq8 in HBs. subst b. reflexivity.
    - destruct (kimg_covr (kn cs) a (Z.of_nat (length bs))) eqn:KI.
      + unfold kimg_covr in KI. apply existsb_exists in KI as [K [HK HB]]. destruct K; try discriminate.
        apply andb_true_iff in HB as [HB H4]. apply andb_true_iff in HB as [HB H3]. apply andb_true_iff in HB as [H1 H2].
        apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
        destruct (rdn BSEGS (fun _ => None) (Z_to_bv 64 a) (length bs)) as [bs'|] eqn:RD; [|discriminate].
        apply bytes_eqb_eq in H. subst bs'.
        assert (KH : khas (KImg lo hi) = true).
        { unfold khas. apply existsb_exists. exists (KImg lo hi). split; [exact HK|]. cbn. rewrite !Z.eqb_refl. reflexivity. }
        destruct (kimg_mb lo hi (a + Z.of_nat i) KH ltac:(lia) H3 H4) as [_ E2]. rewrite E2.
        pose proof (rdn_mbytes (fun _ => None) (length bs) (Z_to_bv 64 a) bs RD i Hi) as X.
        rewrite u_lit64a, Z.mod_small in X by lia. rewrite X. symmetry. apply nth_error_nth'. exact Hi.
      + apply bytes_okb_sound; assumption.
  Qed.

  Lemma cells_okb_sound : forall l, cells_okb l = true ->
    Forall (fun c => 0 <= fst c /\ fst c + Z.of_nat (length (snd c)) <= 2^64 /\
                     forall i, (i < length (snd c))%nat -> mb (fst c + Z.of_nat i) = nth_error (snd c) i) l.
  Proof.
    intros l H. unfold cells_okb in H. apply Forall_forall. intros c Hc.
    pose proof (proj1 (forallb_forall _ _) H c Hc) as X. cbn beta in X.
    apply andb_true_iff in X as [X B]. apply andb_true_iff in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2.
    split; [exact X1|]. split; [exact X2|]. intros i Hi. apply cell_okb_sound; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma kimg_zero_range : forall lo' hi' lo hi,
    khas (KImg lo' hi') = true -> lo' <= lo -> hi <= hi' -> img_lo BOTH <= lo' -> hi' <= img_hi BOTH ->
    (forall a, lo <= a < hi -> seg_rom BSEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
    forall a, lo <= a < hi -> FULL (Z_to_bv 64 a) = None /\ mb a = Some (Z_to_bv 8 0).
  Proof.
    intros lo' hi' lo hi KH H1 H2 Hlo Hhi HZ a Ha.
    destruct (kimg_mb lo' hi' a KH ltac:(lia) ltac:(lia) ltac:(lia)) as [E1 E2]. split; [exact E1|]. rewrite E2. apply HZ. exact Ha.
  Qed.
End Extract.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_NONE : list (Z * Z) :=
  [(0x10000, 0xaaa58); (0xaaa68, 0xaaa70); (0xaaa74, 0xb1500); (0xb1509, 0xb1558); (0xb1570, 0xb1578); (0xb1584, 0xb1588); (0xb1591, 0xb1598); (0xb15c0, 0xb1800); (0xb1804, 0xb1870); (0xb1888, 0xb18c8); (0xb18ca, 0xb2378); (0xb2385, 0xb23b8); (0xb23cd, 0xb23d0); (0xb23e1, 0xb23e4); (0xb23f5, 0xb23f8); (0xb2413, 0xb2414); (0xb2419, 0xb241c); (0xb242c, 0xb2430); (0xb2431, 0xb2438); (0xb2458, 0xb2468); (0xb2478, 0xb2498); (0xb24b0, 0xb24b8); (0xb3768, 0xb43f8); (0xb43fb, 0xb43fc); (0xb4410, 0xb4418); (0xb441d, 0xb4420); (0xb4421, 0xb4424); (0xb4428, 0xb4bb8); (0xb4bc4, 0xb5898); (0xb589c, 0xb58a0); (0xb58a8, 0xb58b8); (0xb58b9, 0xb58bc); (0xb58c0, 0xb5930); (0xb5940, 0xb5c00); (0xb5c08, 0xb5c40); (0xb5c4c, 0xb5c50); (0xb5c6d, 0xb5ca8); (0xb5ca9, 0xb5cb0); (0xb5cb1, 0xb5cb8); (0xb5cd0, 0xb5cd8); (0xb5d2c, 0xb5d30); (0xb5dbc, 0x136e08); (0x136e20, 0x136e21); (0x136e22, 0x144650); (0x14465c, 0x144660); (0x144668, 0x144680); (0x14567f, 0x145680); (0x14667f, 0x1466e0); (0x1466e4, 0x1466e8); (0x146808, 0x1468d0); (0x1468d8, 0x1468f8); (0x146900, 0x146910); (0x146928, 0x146948); (0x146949, 0x146a58); (0x146a59, 0x186a88); (0x186aa8, 0x1a3778); (0x1a377c, 0x219a74); (0x219a78, 0x596a98); (0x596a9c, 0x596aa0); (0x596aa4, 0x596aa8); (0x596ab0, 0x5d6f80); (0x5d6f81, 0x5d6f84); (0x5d6f97, 0x5d6f98); (0x5d6f9c, 0x5d6fa0); (0x5d6fac, 0x5d7140); (0x5d7148, 0x5d7180); (0x5d718c, 0x5d7190); (0x5d71ce, 0x5d71e8); (0x5d71e9, 0x5d71f0); (0x5d71f4, 0x5d71f8); (0x5d71fa, 0x5d7200); (0x5d720a, 0x5e7280); (0x5e7282, 0x5e72c0); (0x5e72c2, 0x5e7b08); (0x5e7b34, 0x5e7b38); (0x5e7b3c, 0x5e7b42); (0x5e7b43, 0x5e7b80); (0x5e7b90, 0x5e7ba8); (0x5e7bb0, 0x5e7bc8); (0x5e7be8, 0x5e7bf8); (0x5e7c08, 0x607bf0); (0x607c20, 0x607c30); (0x607c34, 0x607c38); (0x607c40, 0x607c48); (0x607c50, 0x607d48); (0x607d50, 0x607e58); (0x607e69, 0x607e70); (0x607ea0, 0x607ed0); (0x607ed8, 0x607ee8); (0x607ef8, 0x607f00); (0x607f38, 0x607f48); (0x607f50, 0x607fb0); (0x607fb8, 0x607fd0); (0x607fd8, 0x607ff0); (0x607ff8, 0x6080c8); (0x6080d0, 0x608130); (0x608138, 0x608150); (0x608158, 0x608170); (0x608178, 0x608278); (0x608279, 0x608280); (0x608288, 0x608b30); (0x608b38, 0x608b40); (0x608b48, 0x608f40); (0x608f44, 0x608f48); (0x608f4c, 0x608f80); (0x608f88, 0x60a000)].
Definition IMG_WORDS : list (Z * nat * Z) :=
  [(0xb2470, 8%nat, 0x0); (0xb2430, 1%nat, 0x1); (0xb1508, 1%nat, 0x1); (0xb1500, 8%nat, 0x1); (0xb2438, 8%nat, 0xfc); (0x5e72c0, 1%nat, 0x1); (0xb24a0, 4%nat, 0x4); (0x5e7281, 1%nat, 0x1); (0x5e7280, 1%nat, 0x1); (0x5e72c1, 1%nat, 0x1); (0xb24a4, 4%nat, 0x0); (0xb24a8, 4%nat, 0x80); (0xb24ac, 4%nat, 0x0); (0xb2468, 8%nat, 0xb2498); (0x186aa4, 1%nat, 0x0); (0x186a90, 8%nat, 0x800000); (0x186aa5, 3%nat, 0x0); (0x596aa0, 1%nat, 0x0); (0x596aa1, 3%nat, 0x0); (0x596a98, 4%nat, 0x1); (0xb589a, 1%nat, 0x0); (0xb5c00, 8%nat, 0xb5c40); (0xb5c60, 8%nat, 0x0); (0xb5ca8, 1%nat, 0x1); (0xb5c58, 8%nat, 0x0); (0xb5c50, 8%nat, 0x0); (0xb5c48, 4%nat, 0x5); (0xb5c40, 8%nat, 0xaaa20); (0x5d71f0, 1%nat, 0x0); (0x5d71f1, 1%nat, 0x1); (0x5d7140, 8%nat, 0x5d7180); (0x5d71a0, 8%nat, 0x0); (0x5d71e8, 1%nat, 0x1); (0x5d7198, 8%nat, 0x0); (0x5d7190, 8%nat, 0x0); (0x5d7188, 4%nat, 0x26); (0x5d7180, 8%nat, 0xacff0); (0x5d71f2, 2%nat, 0x0); (0x6080c8, 8%nat, 0xa); (0x608130, 8%nat, 0x2); (0x608150, 8%nat, 0x2); (0x608170, 8%nat, 0x2); (0x607ef4, 4%nat, 0x1); (0x608278, 1%nat, 0x1); (0x607f08, 8%nat, 0x61); (0x607f10, 8%nat, 0x0); (0x607ef0, 4%nat, 0x1); (0xb5d30, 8%nat, 0x0); (0xb5d58, 8%nat, 0x1); (0x146948, 1%nat, 0x1); (0xb1800, 1%nat, 0x0); (0xb1801, 3%nat, 0x0); (0x1468f8, 8%nat, 0x1); (0x5e7b42, 1%nat, 0x1); (0xb5d40, 8%nat, 0x1); (0xb5d50, 8%nat, 0x1); (0xb5d48, 8%nat, 0x1); (0xb5d70, 8%nat, 0x1); (0xb5d68, 8%nat, 0x1000); (0xb5cc8, 8%nat, 0x0); (0xb5d10, 4%nat, 0x0); (0xb5d08, 4%nat, 0x0); (0xb5d00, 8%nat, 0x0); (0xb5cf8, 8%nat, 0x0); (0xb5cc0, 8%nat, 0xb5ce8); (0xb5cb0, 1%nat, 0x1); (0xb5cf4, 4%nat, 0x0); (0xb5cf0, 4%nat, 0x0); (0xb5ce8, 8%nat, 0x0); (0xb5d14, 4%nat, 0x0); (0xb5d0c, 4%nat, 0x0); (0xb5cb8, 8%nat, 0xb5d18); (0xb5d98, 8%nat, 0x0); (0xb5d90, 8%nat, 0x0); (0xb5d88, 8%nat, 0x0); (0xb5d80, 8%nat, 0x0); (0xb5d78, 8%nat, 0x0); (0xb5db8, 4%nat, 0x0); (0xb5db0, 8%nat, 0x0); (0xb5da8, 8%nat, 0x0); (0xb5da0, 8%nat, 0x0); (0xb5d3c, 4%nat, 0x0); (0xb5d38, 4%nat, 0x0); (0xb5d28, 4%nat, 0x0); (0xb5d20, 8%nat, 0xffffffffffffffff); (0xb5d18, 8%nat, 0x640c8); (0x146920, 8%nat, 0x76258); (0x607c30, 4%nat, 0x1); (0x607d48, 8%nat, 0x76258); (0x607c48, 8%nat, 0x98320); (0x607c38, 8%nat, 0x607c40); (0x146a58, 1%nat, 0x0); (0xb5898, 1%nat, 0x1); (0xb5899, 1%nat, 0x1); (0xb2378, 8%nat, 0x10000000000); (0xb2382, 2%nat, 0x800); (0xb2380, 2%nat, 0x10); (0xb2384, 1%nat, 0x1); (0xb18c9, 1%nat, 0x0); (0xb18c8, 1%nat, 0x0); (0xb1880, 8%nat, 0x100000); (0xb1878, 8%nat, 0xe666661); (0xb1870, 8%nat, 0x10000000); (0xb15b8, 8%nat, 0x1981a); (0xb15b0, 8%nat, 0x800000); (0xb1598, 8%nat, 0x1000); (0xb1580, 4%nat, 0xffffffffffffffff); (0xb5938, 8%nat, 0x1000); (0xb5930, 8%nat, 0x1); (0xb1568, 8%nat, 0x16e47); (0xb1560, 8%nat, 0x2000011000); (0xb1590, 1%nat, 0x0); (0x136e21, 1%nat, 0x1); (0x608f48, 4%nat, 0x0); (0x608b40, 8%nat, 0x5ae5c); (0x608f40, 4%nat, 0x0); (0xb4424, 4%nat, 0x0); (0x5e7b80, 8%nat, 0x608f80); (0xb4420, 1%nat, 0x1); (0xb4bb8, 8%nat, 0x7fff8000); (0xb43fa, 1%nat, 0x1); (0xb43f8, 1%nat, 0x1); (0xb43fc, 4%nat, 0x12b); (0xb4400, 8%nat, 0xb4408); (0xb43f9, 1%nat, 0x1); (0x136e18, 8%nat, 0x601bc); (0xaaa58, 8%nat, 0x8); (0xb4bc0, 4%nat, 0x1); (0x1466e0, 1%nat, 0x0); (0xaaa70, 4%nat, 0x2); (0x1466e1, 3%nat, 0x0); (0x1468d0, 8%nat, 0x5b060); (0x146910, 8%nat, 0x60130); (0x146918, 8%nat, 0x60048); (0xb58a0, 8%nat, 0x7fffffffffff); (0xb58bc, 4%nat, 0x1e); (0xb441c, 1%nat, 0x1); (0xb4418, 4%nat, 0x2); (0xb2406, 1%nat, 0x1); (0x1466e8, 8%nat, 0x1); (0x1466f0, 8%nat, 0x0); (0x1466f8, 8%nat, 0x0); (0x146700, 8%nat, 0x140b6); (0x146708, 8%nat, 0x1e00010000); (0x146710, 8%nat, 0x0); (0x146718, 8%nat, 0x0); (0x146720, 8%nat, 0x0); (0x146728, 8%nat, 0x0); (0x146730, 8%nat, 0x10101000101); (0x146738, 8%nat, 0x100000000); (0x146740, 8%nat, 0x0); (0x146748, 8%nat, 0x0); (0x146750, 8%nat, 0x0); (0x146758, 8%nat, 0x10001); (0x146760, 8%nat, 0xffffffffffffffff); (0x146768, 8%nat, 0x118c7); (0x146770, 8%nat, 0x100); (0x146778, 8%nat, 0x0); (0x146780, 8%nat, 0x0); (0x146788, 8%nat, 0x0); (0x146790, 8%nat, 0x0); (0x146798, 8%nat, 0xffffffff00000000); (0x1467a0, 8%nat, 0x1); (0x1467a8, 8%nat, 0x14412); (0x1467b0, 8%nat, 0x140b6); (0x1467b8, 8%nat, 0x140b6); (0x1467c0, 8%nat, 0x10101000100); (0x1467c8, 8%nat, 0x0); (0x1467d0, 8%nat, 0x1e22e); (0x1467d8, 8%nat, 0x101000100000000); (0x1467e0, 8%nat, 0x101010101010101); (0x1467e8, 8%nat, 0x1010101); (0x1467f0, 8%nat, 0x10100000001); (0x1467f8, 8%nat, 0x1908c); (0x146800, 8%nat, 0x1000000000100); (0xb23c0, 4%nat, 0x400); (0xb23bc, 4%nat, 0x100); (0x144658, 4%nat, 0x0); (0x5d7208, 2%nat, 0x0); (0x5d7200, 8%nat, 0x140b6); (0x5d71f8, 2%nat, 0x0); (0x5d6fa8, 4%nat, 0x1); (0x5d6f90, 4%nat, 0x101); (0x5d6f88, 8%nat, 0x101010100000000); (0x5d6f84, 4%nat, 0x0); (0x5d6f80, 1%nat, 0x0); (0x5d6fa0, 8%nat, 0x140b6); (0x5d6f98, 4%nat, 0x1); (0x5d6f96, 1%nat, 0x0); (0x5d6f94, 2%nat, 0x0); (0xb2412, 1%nat, 0x0); (0xb23cc, 1%nat, 0x0); (0xb2420, 8%nat, 0x140b6); (0xb241c, 4%nat, 0x2); (0xb2418, 1%nat, 0x1); (0xb2414, 4%nat, 0x0); (0xb2410, 2%nat, 0x1); (0xb2408, 8%nat, 0x101010101000001); (0xb2400, 6%nat, 0x100000000); (0xb2407, 1%nat, 0x0); (0xb23e4, 4%nat, 0x1000); (0xb23e0, 1%nat, 0x0); (0xb23d8, 8%nat, 0x1400000010); (0xb23d0, 8%nat, 0x101010000000001); (0xb23c8, 4%nat, 0x800); (0xb23f8, 8%nat, 0x0); (0xb23f4, 1%nat, 0x1); (0xb23f0, 4%nat, 0x55); (0xb23e8, 8%nat, 0xbe00000000); (0xb23c4, 4%nat, 0x10); (0xb23b8, 4%nat, 0xffffffff); (0xb2428, 4%nat, 0x10101); (0x144660, 8%nat, 0x1000); (0xb58b8, 1%nat, 0x1); (0xaaa60, 8%nat, 0x20bdb); (0xb589b, 1%nat, 0x0); (0x5e8318, 8%nat, 0x0); (0x607c19, 1%nat, 0x0); (0x5e7b28, 8%nat, 0x0); (0x5e7b20, 8%nat, 0x5e7b10); (0x5e7b18, 8%nat, 0x5e7b10); (0x5e7b88, 8%nat, 0x5e7b88); (0x5e7ba8, 8%nat, 0x607ea0); (0x5e7b38, 4%nat, 0x2); (0x607e68, 1%nat, 0x1); (0x5e7b10, 8%nat, 0x5e7b10); (0x5e7bd0, 8%nat, 0x5e7bf8); (0x5e7bf8, 8%nat, 0x1); (0x5e7c00, 8%nat, 0x5e83d8); (0x607e88, 8%nat, 0x8); (0x607e80, 8%nat, 0xf8); (0x607c10, 8%nat, 0x0); (0x607c00, 8%nat, 0x18); (0x607e90, 8%nat, 0x1); (0x607e78, 8%nat, 0x607be8); (0x607c08, 8%nat, 0x8); (0x607bf8, 8%nat, 0x0); (0x607bf0, 8%nat, 0xa73b0); (0x607e98, 8%nat, 0x1000)].
Definition EXT_WORDS : list (Z * nat * Z) :=
  [(0x7fffc86d, 1%nat, 0x5); (0x7fffc865, 1%nat, 0x4); (0x7fffc861, 1%nat, 0x7); (0x7fffc85a, 1%nat, 0x1); (0x7fffc849, 1%nat, 0x2); (0x7fffc840, 1%nat, 0x6); (0x7fffc839, 1%nat, 0x7); (0x7fffc833, 1%nat, 0x6); (0x7fffc828, 1%nat, 0x2); (0x7fffc819, 1%nat, 0x6); (0x7fffc812, 1%nat, 0x3); (0x7fffc80d, 1%nat, 0x1); (0x7fffc806, 1%nat, 0x7); (0x7fffc7fa, 1%nat, 0x3); (0x7fffc7f0, 1%nat, 0x6); (0x7fffc7ec, 1%nat, 0x5); (0x7fffc7e8, 1%nat, 0x5); (0x7fffc7e4, 1%nat, 0x7); (0x7fffc7e0, 1%nat, 0x7); (0x7fffc7dc, 1%nat, 0x6); (0x7fffc7d6, 1%nat, 0x2); (0x7fffc7c9, 1%nat, 0x4); (0x7fffc7c1, 1%nat, 0x1); (0x7fffc7bd, 1%nat, 0x5); (0x7fffc7b4, 1%nat, 0x7); (0x7fffc7a5, 1%nat, 0x3); (0x7fffc798, 1%nat, 0x5); (0x7fffc78c, 1%nat, 0x6); (0x7fffc785, 1%nat, 0x7); (0x7fffc77c, 1%nat, 0x2); (0x7fffc775, 1%nat, 0x7); (0x7fffc771, 1%nat, 0x1); (0x7fffc76c, 1%nat, 0x5); (0x7fffc764, 1%nat, 0x7); (0x7fffc75a, 1%nat, 0x2); (0x7fffc755, 1%nat, 0x1); (0x7fffc750, 1%nat, 0x5); (0x7fffc74c, 1%nat, 0x6); (0x7fffc748, 1%nat, 0x4); (0x7fffc744, 1%nat, 0x7); (0x7fffc740, 1%nat, 0x7); (0x7fffc73c, 1%nat, 0x4); (0x7fffc738, 1%nat, 0x7); (0x7fffc732, 1%nat, 0x2); (0x7fffc728, 1%nat, 0x1); (0x7fffc71b, 1%nat, 0x4); (0x7fffc712, 1%nat, 0x7); (0x7fffc70d, 1%nat, 0x3); (0x7fffc708, 1%nat, 0x3); (0x7fffc6ff, 1%nat, 0x6); (0x7fffc6f7, 1%nat, 0x3); (0x7fffc6f1, 1%nat, 0x6); (0x7fffc6eb, 1%nat, 0x2); (0x7fffc6e5, 1%nat, 0x5); (0x7fffc6e1, 1%nat, 0x1); (0x7fffc6da, 1%nat, 0x7); (0x7fffc6d4, 1%nat, 0x7); (0x7fffc6ce, 1%nat, 0x2); (0x7fffc6c9, 1%nat, 0x3); (0x7fffc6c3, 1%nat, 0x2); (0x7fffc6b8, 1%nat, 0x1); (0x7fffc6a0, 1%nat, 0x4); (0x7fffc699, 1%nat, 0x4); (0x7fffc695, 1%nat, 0x7); (0x7fffc68f, 1%nat, 0x2); (0x7fffc689, 1%nat, 0x4); (0x7fffc67e, 1%nat, 0x5); (0x7fffc676, 1%nat, 0x7); (0x7fffc66c, 1%nat, 0x5); (0x7fffc665, 1%nat, 0x4); (0x7fffc65c, 1%nat, 0x7); (0x7fffc652, 1%nat, 0x4); (0x7fffc64b, 1%nat, 0x4); (0x7fffc645, 1%nat, 0x4); (0x7fffc63c, 1%nat, 0x7); (0x7fffc632, 1%nat, 0x5); (0x7fffc629, 1%nat, 0x6); (0x7fffc625, 1%nat, 0x5); (0x7fffc618, 1%nat, 0x7); (0x7fffc611, 1%nat, 0x3); (0x7fffc60a, 1%nat, 0x5); (0x7fffc601, 1%nat, 0x6); (0x7fffc5fd, 1%nat, 0x1); (0x7fffc5f9, 1%nat, 0x2); (0x7fffc5f4, 1%nat, 0x4); (0x7fffc5e9, 1%nat, 0x7); (0x7fffc5e1, 1%nat, 0x5); (0x7fffc5d8, 1%nat, 0x4); (0x7fffc5d5, 1%nat, 0x2); (0x7fffc5d1, 1%nat, 0x2); (0x7fffc5cd, 1%nat, 0x3); (0x7fffc5c6, 1%nat, 0x1); (0x7fffc5b9, 1%nat, 0x1); (0x7fffc5b2, 1%nat, 0x2); (0x7fffc5a5, 1%nat, 0x3); (0x7fffc5a1, 1%nat, 0x2); (0x7fffc59d, 1%nat, 0x1); (0x7fffc598, 1%nat, 0x6); (0x7fffc586, 1%nat, 0x2); (0x7fffc57e, 1%nat, 0x3); (0x7fffc578, 1%nat, 0x1); (0x7fffc574, 1%nat, 0x6); (0x7fffc56f, 1%nat, 0x3); (0x7fffc569, 1%nat, 0x6); (0x7fffc561, 1%nat, 0x2); (0x7fffc55a, 1%nat, 0x1); (0x7fffc552, 1%nat, 0x1); (0x7fffc54d, 1%nat, 0x6); (0x7fffc547, 1%nat, 0x2); (0x7fffc541, 1%nat, 0x5); (0x7fffc530, 1%nat, 0x3); (0x7fffc526, 1%nat, 0x2); (0x7fffc51e, 1%nat, 0x7); (0x7fffc516, 1%nat, 0x7); (0x7fffc50a, 1%nat, 0x6); (0x7fffc501, 1%nat, 0x7); (0x7fffc4fd, 1%nat, 0x6); (0x7fffc4f9, 1%nat, 0x3); (0x7fffc4f2, 1%nat, 0x4); (0x7fffc4ea, 1%nat, 0x2); (0x7fffc4e5, 1%nat, 0x4); (0x7fffc4de, 1%nat, 0x5); (0x7fffc4d6, 1%nat, 0x2); (0x7fffc4d1, 1%nat, 0x4); (0x7fffc4ca, 1%nat, 0x2); (0x7fffc4c1, 1%nat, 0x1); (0x7fffc4bd, 1%nat, 0x1); (0x7fffc4b9, 1%nat, 0x4); (0x7fffc4b5, 1%nat, 0x3); (0x7fffc4b1, 1%nat, 0x1); (0x7fffc4a9, 1%nat, 0x1); (0x7fffc4a1, 1%nat, 0x2); (0x7fffc49d, 1%nat, 0x5); (0x7fffc499, 1%nat, 0x3); (0x7fffc494, 1%nat, 0x2); (0x7fffc491, 1%nat, 0x1); (0x7fffc48c, 1%nat, 0x1); (0x7fffc486, 1%nat, 0x6); (0x7fffc47a, 1%nat, 0x6); (0x7fffc471, 1%nat, 0x4); (0x7fffc46c, 1%nat, 0x3); (0x7fffc465, 1%nat, 0x4); (0x7fffc45d, 1%nat, 0x4); (0x7fffc454, 1%nat, 0x3); (0x7fffc44a, 1%nat, 0x3); (0x7fffc443, 1%nat, 0x5); (0x7fffc434, 1%nat, 0x4); (0x7fffc428, 1%nat, 0x6); (0x7fffc41d, 1%nat, 0x4); (0x7fffc40d, 1%nat, 0x5); (0x7fffc407, 1%nat, 0x6); (0x7fffc401, 1%nat, 0x7); (0x7fffc3fd, 1%nat, 0x6); (0x7fffc3f8, 1%nat, 0x7); (0x7fffc3f5, 1%nat, 0x1); (0x7fffc3f0, 1%nat, 0x6); (0x7fffc3eb, 1%nat, 0x6); (0x7fffc3e5, 1%nat, 0x4); (0x7fffc3e0, 1%nat, 0x7); (0x7fffc3dd, 1%nat, 0x2); (0x7fffc3d6, 1%nat, 0x6); (0x7fffc3d1, 1%nat, 0x7); (0x7fffc3cd, 1%nat, 0x2); (0x7fffc3c9, 1%nat, 0x1); (0x7fffc3c5, 1%nat, 0x1); (0x7fffc3c1, 1%nat, 0x3); (0x7fffc3ba, 1%nat, 0x1); (0x7fffc3b3, 1%nat, 0x1); (0x7fffc3ab, 1%nat, 0x1); (0x7fffc3a5, 1%nat, 0x2); (0x7fffc3a1, 1%nat, 0x1); (0x7fffc398, 1%nat, 0x3); (0x7fffc391, 1%nat, 0x5); (0x7fffc38a, 1%nat, 0x2); (0x7fffc385, 1%nat, 0x4); (0x7fffc381, 1%nat, 0x6); (0x7fffc377, 1%nat, 0x2); (0x7fffc36f, 1%nat, 0x6); (0x7fffc369, 1%nat, 0x5); (0x7fffc365, 1%nat, 0x5); (0x7fffc35f, 1%nat, 0x1); (0x7fffc356, 1%nat, 0x1); (0x7fffc351, 1%nat, 0x7); (0x7fffc34d, 1%nat, 0x7); (0x7fffc349, 1%nat, 0x7); (0x7fffc343, 1%nat, 0x6); (0x7fffc33d, 1%nat, 0x7); (0x7fffc339, 1%nat, 0x7); (0x7fffc335, 1%nat, 0x7); (0x7fffc32f, 1%nat, 0x2); (0x7fffc329, 1%nat, 0x7); (0x7fffc325, 1%nat, 0x4); (0x7fffc321, 1%nat, 0x6); (0x7fffc31d, 1%nat, 0x4); (0x7fffc319, 1%nat, 0x6); (0x7fffc313, 1%nat, 0x2); (0x7fffc30d, 1%nat, 0x5); (0x7fffc305, 1%nat, 0x2); (0x7fffc301, 1%nat, 0x3); (0x7fffc2fc, 1%nat, 0x2); (0x7fffc2f8, 1%nat, 0x4); (0x7fffc2f5, 1%nat, 0x4); (0x7fffc2e2, 1%nat, 0x7)].
Definition ZERO_LIT : list (Z * Z) :=
  [(0xb5c68, 5); (0x5d71a8, 38); (0x7fffa000, 8930); (0x7fffc2e8, 13); (0x7fffc300, 1); (0x7fffc304, 1); (0x7fffc308, 5); (0x7fffc310, 3); (0x7fffc318, 1); (0x7fffc31c, 1); (0x7fffc320, 1); (0x7fffc324, 1); (0x7fffc328, 1); (0x7fffc32c, 3); (0x7fffc334, 1); (0x7fffc338, 1); (0x7fffc33c, 1); (0x7fffc340, 3); (0x7fffc348, 1); (0x7fffc34c, 1); (0x7fffc350, 1); (0x7fffc354, 2); (0x7fffc35c, 3); (0x7fffc364, 1); (0x7fffc368, 1); (0x7fffc36c, 3); (0x7fffc374, 3); (0x7fffc37c, 1); (0x7fffc380, 1); (0x7fffc384, 1); (0x7fffc388, 2); (0x7fffc390, 1); (0x7fffc394, 4); (0x7fffc3a0, 1); (0x7fffc3a4, 1); (0x7fffc3a8, 3); (0x7fffc3b0, 3); (0x7fffc3b8, 2); (0x7fffc3c0, 1); (0x7fffc3c4, 1); (0x7fffc3c8, 1); (0x7fffc3cc, 1); (0x7fffc3d0, 1); (0x7fffc3d4, 2); (0x7fffc3dc, 1); (0x7fffc3e4, 1); (0x7fffc3e8, 3); (0x7fffc3f4, 1); (0x7fffc3fc, 1); (0x7fffc400, 1); (0x7fffc404, 3); (0x7fffc40c, 1); (0x7fffc410, 13); (0x7fffc424, 4); (0x7fffc430, 4); (0x7fffc43c, 7); (0x7fffc448, 2); (0x7fffc450, 4); (0x7fffc45c, 1); (0x7fffc460, 5); (0x7fffc470, 1); (0x7fffc474, 6); (0x7fffc480, 6); (0x7fffc490, 1); (0x7fffc498, 1); (0x7fffc49c, 1); (0x7fffc4a0, 1); (0x7fffc4a4, 5); (0x7fffc4ac, 5); (0x7fffc4b4, 1); (0x7fffc4b8, 1); (0x7fffc4bc, 1); (0x7fffc4c0, 1); (0x7fffc4c4, 1); (0x7fffc4c8, 2); (0x7fffc4d0, 1); (0x7fffc4d4, 2); (0x7fffc4dc, 2); (0x7fffc4e4, 1); (0x7fffc4e8, 2); (0x7fffc4f0, 2); (0x7fffc4f8, 1); (0x7fffc4fc, 1); (0x7fffc500, 1); (0x7fffc504, 2); (0x7fffc508, 2); (0x7fffc510, 2); (0x7fffc514, 2); (0x7fffc51c, 2); (0x7fffc524, 2); (0x7fffc52c, 4); (0x7fffc538, 6); (0x7fffc540, 1); (0x7fffc544, 3); (0x7fffc54c, 1); (0x7fffc550, 2); (0x7fffc558, 2); (0x7fffc560, 1); (0x7fffc564, 5); (0x7fffc56c, 3); (0x7fffc57c, 2); (0x7fffc584, 2); (0x7fffc58c, 2); (0x7fffc590, 1); (0x7fffc594, 1); (0x7fffc59c, 1); (0x7fffc5a0, 1); (0x7fffc5a4, 1); (0x7fffc5a8, 10); (0x7fffc5b8, 1); (0x7fffc5bc, 10); (0x7fffc5cc, 1); (0x7fffc5d0, 1); (0x7fffc5d4, 1); (0x7fffc5dc, 1); (0x7fffc5e0, 1); (0x7fffc5e4, 5); (0x7fffc5f0, 1); (0x7fffc5f8, 1); (0x7fffc5fc, 1); (0x7fffc600, 1); (0x7fffc604, 6); (0x7fffc610, 1); (0x7fffc614, 4); (0x7fffc620, 1); (0x7fffc624, 1); (0x7fffc628, 1); (0x7fffc62c, 6); (0x7fffc638, 4); (0x7fffc644, 1); (0x7fffc648, 3); (0x7fffc650, 2); (0x7fffc658, 4); (0x7fffc664, 1); (0x7fffc668, 4); (0x7fffc674, 2); (0x7fffc67c, 2); (0x7fffc684, 2); (0x7fffc688, 1); (0x7fffc68c, 3); (0x7fffc694, 1); (0x7fffc698, 1); (0x7fffc69c, 4); (0x7fffc6a8, 5); (0x7fffc6b4, 4); (0x7fffc6c0, 3); (0x7fffc6c8, 1); (0x7fffc6cc, 2); (0x7fffc6d8, 2); (0x7fffc6e0, 1); (0x7fffc6e4, 1); (0x7fffc6e8, 3); (0x7fffc6f0, 1); (0x7fffc6f4, 3); (0x7fffc6fc, 3); (0x7fffc704, 2); (0x7fffc70c, 1); (0x7fffc710, 2); (0x7fffc718, 3); (0x7fffc720, 2); (0x7fffc724, 4); (0x7fffc730, 2); (0x7fffc754, 1); (0x7fffc758, 2); (0x7fffc760, 1); (0x7fffc768, 1); (0x7fffc770, 1); (0x7fffc774, 1); (0x7fffc778, 4); (0x7fffc784, 1); (0x7fffc788, 4); (0x7fffc794, 4); (0x7fffc7a0, 5); (0x7fffc7ac, 1); (0x7fffc7b0, 4); (0x7fffc7bc, 1); (0x7fffc7c0, 1); (0x7fffc7c4, 5); (0x7fffc7d0, 6); (0x7fffc7f4, 6); (0x7fffc800, 6); (0x7fffc80c, 1); (0x7fffc810, 2); (0x7fffc818, 1); (0x7fffc81c, 4); (0x7fffc824, 4); (0x7fffc830, 3); (0x7fffc838, 1); (0x7fffc83c, 4); (0x7fffc848, 1); (0x7fffc84c, 5); (0x7fffc858, 2); (0x7fffc860, 1); (0x7fffc864, 1); (0x7fffc868, 2); (0x7fffc86c, 1); (0x7fffc870, 4); (0x7fffc878, 64); (0x7fffc8c8, 132); (0x7fffc96c, 512); (0x7fffcbec, 16); (0x7fffcc00, 66813); (0x8000d100, 1); (0x8000d104, 1); (0x8000d108, 1); (0x8000d10c, 1); (0x8000d110, 1); (0x8000d114, 1); (0x8000d118, 1); (0x8000d11c, 1); (0x8000d120, 1); (0x8000d124, 1); (0x8000d128, 1); (0x8000d12c, 1); (0x8000d130, 1); (0x8000d134, 1); (0x8000d138, 1); (0x8000d13c, 2288); (0x8000da30, 14); (0x8000da44, 8); (0x8000da50, 6); (0x8000da5c, 100); (0x8000e2a0, 682921); (0x800b4e4c, 1); (0x800b4e50, 5); (0x800b4e58, 17832)].
Definition FILL_LIT : list (Z * Z * Z) :=
  [(0x8000dac0, 2016, 249); (0x800b4e55, 3, 249); (0x800b4e4d, 3, 249); (0x800b4e49, 3, 249); (0x8000da56, 6, 249); (0x8000da4c, 4, 249); (0x8000da3e, 6, 249); (0x8000da2c, 4, 249); (0x8000d139, 3, 249); (0x8000d135, 3, 249); (0x8000d131, 3, 249); (0x8000d12d, 3, 249); (0x8000d129, 3, 249); (0x8000d125, 3, 249); (0x8000d121, 3, 249); (0x8000d11d, 3, 249); (0x8000d119, 3, 249); (0x8000d115, 3, 249); (0x8000d111, 3, 249); (0x8000d10d, 3, 249); (0x8000d109, 3, 249); (0x8000d105, 3, 249); (0x8000d101, 3, 249); (0x8000d0fd, 3, 249); (0x7fffcbfc, 4, 249); (0x7fffcb6c, 128, 249); (0x7fffc94c, 32, 249); (0x7fffc8b8, 16, 249); (0x7fffc874, 4, 249); (0x7fffc86e, 2, 249); (0x7fffc86a, 2, 249); (0x7fffc866, 2, 249); (0x7fffc862, 2, 249); (0x7fffc85b, 5, 249); (0x7fffc851, 7, 249); (0x7fffc84a, 2, 249); (0x7fffc841, 7, 249); (0x7fffc83a, 2, 249); (0x7fffc834, 4, 249); (0x7fffc829, 7, 249); (0x7fffc820, 4, 249); (0x7fffc81a, 2, 249); (0x7fffc813, 5, 249); (0x7fffc80e, 2, 249); (0x7fffc807, 5, 249); (0x7fffc7fb, 5, 249); (0x7fffc7f1, 3, 249); (0x7fffc7ed, 3, 249); (0x7fffc7e9, 3, 249); (0x7fffc7e5, 3, 249); (0x7fffc7e1, 3, 249); (0x7fffc7dd, 3, 249); (0x7fffc7d7, 5, 249); (0x7fffc7ca, 6, 249); (0x7fffc7c2, 2, 249); (0x7fffc7be, 2, 249); (0x7fffc7b5, 7, 249); (0x7fffc7ad, 3, 249); (0x7fffc7a6, 6, 249); (0x7fffc799, 7, 249); (0x7fffc78d, 7, 249); (0x7fffc786, 2, 249); (0x7fffc77d, 7, 249); (0x7fffc776, 2, 249); (0x7fffc772, 2, 249); (0x7fffc76d, 3, 249); (0x7fffc769, 3, 249); (0x7fffc765, 3, 249); (0x7fffc761, 3, 249); (0x7fffc75b, 5, 249); (0x7fffc756, 2, 249); (0x7fffc751, 3, 249); (0x7fffc74d, 3, 249); (0x7fffc749, 3, 249); (0x7fffc745, 3, 249); (0x7fffc741, 3, 249); (0x7fffc73d, 3, 249); (0x7fffc739, 3, 249); (0x7fffc733, 5, 249); (0x7fffc729, 7, 249); (0x7fffc722, 2, 249); (0x7fffc71c, 4, 249); (0x7fffc713, 5, 249); (0x7fffc70e, 2, 249); (0x7fffc709, 3, 249); (0x7fffc706, 2, 249); (0x7fffc700, 4, 249); (0x7fffc6f8, 4, 249); (0x7fffc6f2, 2, 249); (0x7fffc6ec, 4, 249); (0x7fffc6e6, 2, 249); (0x7fffc6e2, 2, 249); (0x7fffc6db, 5, 249); (0x7fffc6d5, 3, 249); (0x7fffc6cf, 5, 249); (0x7fffc6ca, 2, 249); (0x7fffc6c4, 4, 249); (0x7fffc6b9, 7, 249); (0x7fffc6ad, 7, 249); (0x7fffc6a1, 7, 249); (0x7fffc69a, 2, 249); (0x7fffc696, 2, 249); (0x7fffc690, 4, 249); (0x7fffc68a, 2, 249); (0x7fffc686, 2, 249); (0x7fffc67f, 5, 249); (0x7fffc677, 5, 249); (0x7fffc66d, 7, 249); (0x7fffc666, 2, 249); (0x7fffc65d, 7, 249); (0x7fffc653, 5, 249); (0x7fffc64c, 4, 249); (0x7fffc646, 2, 249); (0x7fffc63d, 7, 249); (0x7fffc633, 5, 249); (0x7fffc62a, 2, 249); (0x7fffc626, 2, 249); (0x7fffc621, 3, 249); (0x7fffc619, 7, 249); (0x7fffc612, 2, 249); (0x7fffc60b, 5, 249); (0x7fffc602, 2, 249); (0x7fffc5fe, 2, 249); (0x7fffc5fa, 2, 249); (0x7fffc5f5, 3, 249); (0x7fffc5f1, 3, 249); (0x7fffc5ea, 6, 249); (0x7fffc5e2, 2, 249); (0x7fffc5dd, 3, 249); (0x7fffc5d9, 3, 249); (0x7fffc5d6, 2, 249); (0x7fffc5d2, 2, 249); (0x7fffc5ce, 2, 249); (0x7fffc5c7, 5, 249); (0x7fffc5ba, 2, 249); (0x7fffc5b3, 5, 249); (0x7fffc5a6, 2, 249); (0x7fffc5a2, 2, 249); (0x7fffc59e, 2, 249); (0x7fffc599, 3, 249); (0x7fffc595, 3, 249); (0x7fffc591, 3, 249); (0x7fffc58e, 2, 249); (0x7fffc587, 5, 249); (0x7fffc57f, 5, 249); (0x7fffc579, 3, 249); (0x7fffc575, 3, 249); (0x7fffc570, 4, 249); (0x7fffc56a, 2, 249); (0x7fffc562, 2, 249); (0x7fffc55b, 5, 249); (0x7fffc553, 5, 249); (0x7fffc54e, 2, 249); (0x7fffc548, 4, 249); (0x7fffc542, 2, 249); (0x7fffc53e, 2, 249); (0x7fffc531, 7, 249); (0x7fffc527, 5, 249); (0x7fffc51f, 5, 249); (0x7fffc517, 5, 249); (0x7fffc512, 2, 249); (0x7fffc50b, 5, 249); (0x7fffc506, 2, 249); (0x7fffc502, 2, 249); (0x7fffc4fe, 2, 249); (0x7fffc4fa, 2, 249); (0x7fffc4f3, 5, 249); (0x7fffc4eb, 5, 249); (0x7fffc4e6, 2, 249); (0x7fffc4df, 5, 249); (0x7fffc4d7, 5, 249); (0x7fffc4d2, 2, 249); (0x7fffc4cb, 5, 249); (0x7fffc4c5, 3, 249); (0x7fffc4c2, 2, 249); (0x7fffc4be, 2, 249); (0x7fffc4ba, 2, 249); (0x7fffc4b6, 2, 249); (0x7fffc4b2, 2, 249); (0x7fffc4aa, 2, 249); (0x7fffc4a2, 2, 249); (0x7fffc49e, 2, 249); (0x7fffc49a, 2, 249); (0x7fffc495, 3, 249); (0x7fffc492, 2, 249); (0x7fffc48d, 3, 249); (0x7fffc487, 5, 249); (0x7fffc47b, 5, 249); (0x7fffc472, 2, 249); (0x7fffc46d, 3, 249); (0x7fffc466, 6, 249); (0x7fffc45e, 2, 249); (0x7fffc455, 7, 249); (0x7fffc44b, 5, 249); (0x7fffc444, 4, 249); (0x7fffc435, 7, 249); (0x7fffc429, 7, 249); (0x7fffc41e, 6, 249); (0x7fffc40e, 2, 249); (0x7fffc408, 4, 249); (0x7fffc402, 2, 249); (0x7fffc3fe, 2, 249); (0x7fffc3f9, 3, 249); (0x7fffc3f6, 2, 249); (0x7fffc3f1, 3, 249); (0x7fffc3ec, 4, 249); (0x7fffc3e6, 2, 249); (0x7fffc3e1, 3, 249); (0x7fffc3de, 2, 249); (0x7fffc3d7, 5, 249); (0x7fffc3d2, 2, 249); (0x7fffc3ce, 2, 249); (0x7fffc3ca, 2, 249); (0x7fffc3c6, 2, 249); (0x7fffc3c2, 2, 249); (0x7fffc3bb, 5, 249); (0x7fffc3b4, 4, 249); (0x7fffc3ac, 4, 249); (0x7fffc3a6, 2, 249); (0x7fffc3a2, 2, 249); (0x7fffc399, 7, 249); (0x7fffc392, 2, 249); (0x7fffc38b, 5, 249); (0x7fffc386, 2, 249); (0x7fffc382, 2, 249); (0x7fffc37d, 3, 249); (0x7fffc378, 4, 249); (0x7fffc370, 4, 249); (0x7fffc36a, 2, 249); (0x7fffc366, 2, 249); (0x7fffc360, 4, 249); (0x7fffc357, 5, 249); (0x7fffc352, 2, 249); (0x7fffc34e, 2, 249); (0x7fffc34a, 2, 249); (0x7fffc344, 4, 249); (0x7fffc33e, 2, 249); (0x7fffc33a, 2, 249); (0x7fffc336, 2, 249); (0x7fffc330, 4, 249); (0x7fffc32a, 2, 249); (0x7fffc326, 2, 249); (0x7fffc322, 2, 249); (0x7fffc31e, 2, 249); (0x7fffc31a, 2, 249); (0x7fffc314, 4, 249); (0x7fffc30e, 2, 249); (0x7fffc306, 2, 249); (0x7fffc302, 2, 249); (0x7fffc2fd, 3, 249); (0x7fffc2f9, 3, 249); (0x7fffc2f6, 2, 249); (0x7fffc2e3, 5, 249)].
Definition WR_LIT : list (Z * Z) :=
  [(0x7fffa000, 0xbf400); (0xa8000, 0x562000)].

(* [comment removed for export] *)
Definition kimg_covb (k : list kentry) (lo hi : Z) : bool :=
  existsb (fun K => match K with KImg lo' hi' => (lo' <=? lo) && (hi <=? hi') | _ => false end)%bool k.
Definition chk_img_none (cs : acs) : bool :=
  forallb (fun p => kimg_covb (kn cs) (fst p) (snd p) && (img_lo BOTH <=? fst p) && (snd p <=? img_hi BOTH))%bool IMG_NONE.
Definition chk_words (cs : acs) (img : bool) (l : list (Z * nat * Z)) : bool :=
  forallb (fun t => match t with (a, w, v) =>
     existsb (kentry_eqb (KWord (SA (ELit 0) a) w (ELit v))) (kn cs)
     && (if img then (img_lo BOTH <=? a) && (a + Z.of_nat w <=? img_hi BOTH) else (img_hi BOTH <=? a) && (a + Z.of_nat w <=? CEIL)) end)%bool l.
Definition chk_zero (cs : acs) : bool :=
  forallb (fun p => existsb (kentry_eqb (KZero (SA (ELit 0) (fst p)) (ELit (snd p)))) (kn cs) && (0 <=? snd p) && (snd p <? 2^64))%bool ZERO_LIT.
Definition chk_fill (cs : acs) : bool :=
  forallb (fun t => match t with (a, n, c) => existsb (kentry_eqb (KFill (SA (ELit 0) a) (ELit n) c)) (kn cs) && (0 <=? n) && (n <? 2^64) end)%bool FILL_LIT.
Definition chk_wr (cs : acs) : bool :=
  forallb (fun p => existsb (kentry_eqb (KWr (SA (ELit 0) (fst p)) (ELit (snd p)))) (kn cs)) WR_LIT.
(* [comment removed for export] *)
Definition e_sp0' : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6)).
Definition e_p0a : expr :=
  EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))))) (ELit 184).
Definition e_p1 : expr :=
  EMd Instr.M_MUL (EAlu Instr.ALU_SLTU (ELit 1) (EVar 1))
    (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
       (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EAlu Instr.ALU_ADD (EVar 3) (EMd Instr.M_MUL (ELit 16) (EVar 6)))))) (ELit 185)).
Definition chk_regs (cs : acs) : bool :=
  (expr_eqb (sr_get (s_regs (a_ss cs)) 1) (ELit 0x97c74)
   && expr_eqb (sr_get (s_regs (a_ss cs)) 2) (EAlu Instr.ALU_ADD e_sp0' (ELit (-48)))
   && expr_eqb (sr_get (s_regs (a_ss cs)) 3) (ELit 0x10800)
   && expr_eqb (sr_get (s_regs (a_ss cs)) 4) (ELit 0x5e7bd8)
   && expr_eqb (sr_get (s_regs (a_ss cs)) 10) (EVar 1)
   && expr_eqb (sr_get (s_regs (a_ss cs)) 11) (EAlu Instr.ALU_ADD e_sp0' (ELit 8)))%bool.
Definition chk_stack (cs : acs) : bool :=
  (existsb (kentry_eqb (KWr (SA e_sp0' (-8388608)) (ELit 8388608))) (kn cs)
   && existsb (kentry_eqb (KWord (SA e_sp0' 8) 8 e_p0a)) (kn cs)
   && existsb (kentry_eqb (KWord (SA e_sp0' 16) 8 e_p1)) (kn cs)
   && existsb (kentry_eqb (KWord (SA (ELit 0) 0x5e7b30) 4 (EVar 44))) (kn cs)
   && existsb (kentry_eqb (KRange (EVar 44) 1 4194303)) (kn cs))%bool.
Definition chk_all (cs : acs) : bool :=
  (chk_img_none cs && chk_words cs true IMG_WORDS && chk_words cs false EXT_WORDS && chk_zero cs && chk_fill cs && chk_wr cs
   && chk_regs cs && chk_stack cs && afd_eqb (a_fd cs) FdStd)%bool.

(* [comment removed for export] *)
Definition chk_words_m (M : kentry -> bool) (cs : acs) (img : bool) (l : list (Z * nat * Z)) : bool :=
  forallb (fun t => match t with (a, w, v) =>
     M (KWord (SA (ELit 0) a) w (ELit v))
     && (if img then (img_lo BOTH <=? a) && (a + Z.of_nat w <=? img_hi BOTH) else (img_hi BOTH <=? a) && (a + Z.of_nat w <=? CEIL)) end)%bool l.
Definition chk_zero_m (M : kentry -> bool) (cs : acs) : bool :=
  forallb (fun p => M (KZero (SA (ELit 0) (fst p)) (ELit (snd p))) && (0 <=? snd p) && (snd p <? 2^64))%bool ZERO_LIT.
Definition chk_fill_m (M : kentry -> bool) (cs : acs) : bool :=
  forallb (fun t => match t with (a, n, c) => M (KFill (SA (ELit 0) a) (ELit n) c) && (0 <=? n) && (n <? 2^64) end)%bool FILL_LIT.
Definition chk_wr_m (M : kentry -> bool) (cs : acs) : bool :=
  forallb (fun p => M (KWr (SA (ELit 0) (fst p)) (ELit (snd p)))) WR_LIT.
Definition chk_stack_m (M : kentry -> bool) (cs : acs) : bool :=
  (M (KWr (SA e_sp0' (-8388608)) (ELit 8388608))
   && M (KWord (SA e_sp0' 8) 8 e_p0a)
   && M (KWord (SA e_sp0' 16) 8 e_p1)
   && M (KWord (SA (ELit 0) 0x5e7b30) 4 (EVar 44))
   && M (KRange (EVar 44) 1 4194303))%bool.
Definition chk_all_m (M : kentry -> bool) (cs : acs) : bool :=
  (chk_img_none cs && chk_words_m M cs true IMG_WORDS && chk_words_m M cs false EXT_WORDS && chk_zero_m M cs && chk_fill_m M cs && chk_wr_m M cs
   && chk_regs cs && chk_stack_m M cs && afd_eqb (a_fd cs) FdStd)%bool.
Lemma chk_all_m_ref : forall cs, chk_all_m (fun K => existsb (kentry_eqb K) (kn cs)) cs = chk_all cs.
Proof. reflexivity. Qed.
Lemma forallb_ext_chk : forall (T : Type) (f g : T -> bool) l, (forall x, f x = g x) -> forallb f l = forallb g l.
Proof. intros T f g l H. induction l as [|x r IH]; [reflexivity|]. cbn [forallb]. rewrite (H x), IH. reflexivity. Qed.
Lemma chk_all_m_ext : forall (M M' : kentry -> bool) cs, (forall K, M K = M' K) -> chk_all_m M cs = chk_all_m M' cs.
Proof.
  intros M M' cs H. unfold chk_all_m, chk_words_m, chk_zero_m, chk_fill_m, chk_wr_m, chk_stack_m.
  rewrite !H.
  rewrite (forallb_ext_chk _ (fun t => match t with (a, w, v) => M (KWord (SA (ELit 0) a) w (ELit v)) && _ end)%bool
                             (fun t => match t with (a, w, v) => M' (KWord (SA (ELit 0) a) w (ELit v)) && _ end)%bool IMG_WORDS)
    by (intros [[a w] v]; rewrite H; reflexivity).
  rewrite (forallb_ext_chk _ (fun t => match t with (a, w, v) => M (KWord (SA (ELit 0) a) w (ELit v)) && _ end)%bool
                             (fun t => match t with (a, w, v) => M' (KWord (SA (ELit 0) a) w (ELit v)) && _ end)%bool EXT_WORDS)
    by (intros [[a w] v]; rewrite H; reflexivity).
  rewrite (forallb_ext_chk _ (fun p => M (KZero (SA (ELit 0) (fst p)) (ELit (snd p))) && _ && _)%bool
                             (fun p => M' (KZero (SA (ELit 0) (fst p)) (ELit (snd p))) && _ && _)%bool ZERO_LIT) by (intros p; rewrite H; reflexivity).
  rewrite (forallb_ext_chk _ (fun t => match t with (a, n, c) => M (KFill (SA (ELit 0) a) (ELit n) c) && _ && _ end)%bool
                             (fun t => match t with (a, n, c) => M' (KFill (SA (ELit 0) a) (ELit n) c) && _ && _ end)%bool FILL_LIT)
    by (intros [[a n] c]; rewrite H; reflexivity).
  rewrite (forallb_ext_chk _ (fun p => M (KWr (SA (ELit 0) (fst p)) (ELit (snd p)))) (fun p => M' (KWr (SA (ELit 0) (fst p)) (ELit (snd p)))) WR_LIT)
    by (intros p; rewrite H; reflexivity).
  reflexivity.
Qed.
Lemma chk_all_fast : forall cs, chk_all_m (Boots35.BFXE.mem' (Boots35.BFXE.build (kn cs))) cs = true -> chk_all cs = true.
Proof.
  intros cs H. rewrite <- chk_all_m_ref.
  rewrite (chk_all_m_ext _ (Boots35.BFXE.mem' (Boots35.BFXE.build (kn cs))) cs); [exact H|].
  intros K. symmetry. apply Boots35.BFXE.mem'_eq.
Qed.
Lemma chk_all_1 : chk_all HS_both2_1 = true. Proof. apply chk_all_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_all_2 : chk_all HS_both2_2 = true. Proof. apply chk_all_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_all_3 : chk_all HS_both2b_1 = true. Proof. apply chk_all_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_all_4 : chk_all HS_both2b_2 = true. Proof. apply chk_all_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma u_mul64_boot : forall a b : word, bv_unsigned (Sem.mul_div Instr.M_MUL a b) = (bv_unsigned a * bv_unsigned b) mod 2^64.
Proof. intros. cbn [Sem.mul_div]. rewrite bv_mul_unsigned, bv_wrap64_mod. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Main.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  #[local] Notation SINV := (SINV0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 BPH sp rdraw argv envp uid hw).
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  #[local] Notation LIM := (@AsanInit.blim BL).

  Definition usp : Z := bv_unsigned sp.
  Definition argc : Z := Z.of_nat (length argv).
  Definition envc : Z := Z.of_nat (length envp).
  Definition L0 : Z := Z.of_nat (length (nth 0 argv [])).
  (* [comment removed for export] *)
  Definition p0a : Z := usp + 8 * argc + 8 * envc + 184.   (* [comment removed for export] *)
  Definition p1a : Z := p0a + L0 + 1.

  (* [comment removed for export] *)
  Record main_pre (R : bvmap 5 word) (FULL : word -> option byte) (md : Model) : Prop := {
    mp_ra  : getr R 1 = Z_to_bv 64 0x97c74;
    mp_sp  : getr R 2 = Z_to_bv 64 (usp - 48);
    mp_gp  : getr R 3 = Z_to_bv 64 0x10800;
    mp_tp  : getr R 4 = Z_to_bv 64 0x5e7bd8;
    mp_a0  : getr R 10 = Z_to_bv 64 argc;
    mp_a1  : getr R 11 = Z_to_bv 64 (usp + 8);
    mp_halt : m_halted md = None;
    mp_fs   : m_fs md = fs;
    mp_fds  : m_fds md = fds_std;
    mp_limit : vm_limit (m_vmmaps md) = LIM;
    (* [comment removed for export] *)
    mp_tid  : exists tid, 1 <= tid <= 4194303 /\ rdn BSEGS FULL (Z_to_bv 64 0x5e7b30) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
    (* [comment removed for export] *)
    mp_argblock : forall a, argH (E0 BPH sp rdraw brk0 argv envp uid hw) a = true -> FULL a = wrap_mem BPH sp argv envp uid hw rdraw a;
    (* [comment removed for export] *)
    mp_argv0p : forall j, (j < 8)%nat -> FULL (Z_to_bv 64 (usp + 8 + Z.of_nat j)) = Some (nth j (word_to_le_bytes 8 (Z_to_bv 64 p0a)) (Z_to_bv 8 0));
    mp_argv1p : 2 <= argc -> forall j, (j < 8)%nat -> FULL (Z_to_bv 64 (usp + 16 + Z.of_nat j)) = Some (nth j (word_to_le_bytes 8 (Z_to_bv 64 p1a)) (Z_to_bv 8 0));
    (* [comment removed for export] *)
    mp_stack : forall i, 0 <= i < 8388608 -> FULL (Z_to_bv 64 (usp - 8388608 + i)) <> None;
    (* [comment removed for export] *)
    mp_img_none : forall lo hi a, In (lo, hi) IMG_NONE -> lo <= a < hi -> FULL (Z_to_bv 64 a) = None;
    mp_img_words : forall a w v, In (a, w, v) IMG_WORDS -> rdn BSEGS FULL (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v));
    (* [comment removed for export] *)
    mp_ext_words : forall a w v, In (a, w, v) EXT_WORDS ->
        forall j, (j < w)%nat -> FULL (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j (word_to_le_bytes w (Z_to_bv 64 v)) (Z_to_bv 8 0));
    mp_zero : forall a n, In (a, n) ZERO_LIT -> forall i, 0 <= i < n -> FULL (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0);
    mp_fill : forall a n c, In (a, n, c) FILL_LIT -> forall i, 0 <= i < n -> FULL (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 c)
  }.
  (* [comment removed for export] *)
  Section Derive.
    Variable cs : acs.
    Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
    Hypothesis CHK : chk_all cs = true.
    Hypothesis CS : cs_ok BSEGS BOTH LIM SINV argH fs E cs R FULL model.

    Let V0 := pre_v0 sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS.
    Let V6 := pre_v6 sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS.
    Let V1 := pre_v1 sp rdraw brk0 argv envp uid hw fs Hva cs E R FULL model CS.

    Lemma usp_range : 0x7fff80000000 <= usp <= 2^47 /\ usp mod 16 = 0.
    Proof. unfold usp. pose proof Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in *. lia. Qed.
    Lemma argc_range : 1 <= argc <= 1024.
    Proof. unfold argc. pose proof Hva as [H _]. lia. Qed.
    Lemma envc_range : 0 <= envc <= 256.
    Proof. unfold envc. pose proof Hve as [H _]. lia. Qed.
    Lemma L0_range : 0 <= L0 <= 131071.
    Proof.
      unfold L0. pose proof Hva as (H1 & _ & H3 & _). destruct argv as [|a0 r]; cbn [nth length]; [lia|].
      inversion H3. cbn [length] in H1. lia.
    Qed.

    Lemma U_v2 : bv_unsigned (ev E 2%nat) = envc.
    Proof.
      rewrite (pre_ev_lt9 sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS 2%nat) by (unfold NX0; lia). unfold E0. cbn [ev vals0 nth].
      pose proof envc_range. unfold envc in *. rewrite u_lit64a. apply Z.mod_small. lia.
    Qed.
    Lemma U_v3 : bv_unsigned (ev E 3%nat) = L0.
    Proof.
      rewrite (pre_ev_lt9 sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS 3%nat) by (unfold NX0; lia). unfold E0. cbn [ev vals0 nth].
      pose proof L0_range. unfold L0 in *. rewrite u_lit64a. apply Z.mod_small. lia.
    Qed.

    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    Lemma usp_decomp : forall u, 140735340871680 <= u <= 2 ^ 47 -> u mod 16 = 0 ->
      ((32768 * (u / 32768)) mod 2 ^ 64 + (16 * (u mod 32768 / 16)) mod 2 ^ 64) mod 2 ^ 64 = u.
    Proof. intros u UR UA. lia. Qed.

    Lemma usp_split : 32768 * (usp / 32768) + 16 * (usp mod 32768 / 16) = usp
                      /\ 0 <= 32768 * (usp / 32768) <= usp /\ 0 <= 16 * (usp mod 32768 / 16) < 32768.
    Proof. pose proof usp_range as [UR UA]. lia. Qed.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    Lemma U_sp0 : bv_unsigned (edenot E e_sp0') = usp.
    Proof.
      unfold e_sp0'. cbn [edenot]. rewrite u_add64, !u_mul64_boot, !u_lit64a.
      pose proof usp_range as [UR UA]. unfold usp in *. rewrite V0, V6.
      rewrite !(Z.mod_small 32768), !(Z.mod_small 16) by lia. apply usp_decomp; assumption.
    Qed.

    Lemma chk_split :
      chk_img_none cs = true /\ chk_words cs true IMG_WORDS = true /\ chk_words cs false EXT_WORDS = true /\ chk_zero cs = true
      /\ chk_fill cs = true /\ chk_wr cs = true /\ chk_regs cs = true /\ chk_stack cs = true /\ afd_eqb (a_fd cs) FdStd = true.
    Proof. pose proof CHK as C. unfold chk_all in C. do 8 (apply andb_prop in C as [C ?]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption. Qed.

    Theorem main_pre_of_cs_ok : main_pre R FULL model.
    Proof.
      (first [ dand9 chk_split as Cimg Cw Cx Cz Cf Cwr Cregs Cstk Cfd | destruct chk_split as (Cimg & Cw & Cx & Cz & Cf & Cwr & Cregs & Cstk & Cfd) ]).
      pose proof usp_range as [UR UA]. pose proof argc_range as AR. pose proof envc_range as ER. pose proof L0_range as LR.
      pose proof (pre_reg sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS) as REG.
      unfold chk_regs in Cregs. do 5 (apply andb_prop in Cregs as [Cregs ?]).
      repeat match goal with H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H end.
      unfold chk_stack in Cstk. do 4 (apply andb_prop in Cstk as [Cstk ?]).
      split.
      - rewrite REG, Cregs. cbn [edenot]. reflexivity.
      - rewrite REG, H3. apply bv_eq. change (edenot E (EAlu Instr.ALU_ADD e_sp0' (ELit (-48)))) with (Sem.alu64 Instr.ALU_ADD (edenot E e_sp0') (edenot E (ELit (-48)))).
        rewrite u_add64, U_sp0. cbn [edenot]. rewrite !u_lit64a. change ((-48) mod 2^64) with (2^64 - 48).
        rewrite (Z.mod_small (usp - 48)) by lia.
        replace (usp + (2^64 - 48)) with ((usp - 48) + 1 * 2^64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
      - rewrite REG, H2. cbn [edenot]. reflexivity.
      - rewrite REG, H1. cbn [edenot]. reflexivity.
      - rewrite REG, H0. cbn [edenot]. apply bv_eq. rewrite V1, u_lit64a. unfold argc in *. rewrite Z.mod_small by lia. reflexivity.
      - rewrite REG, H. apply bv_eq. change (edenot E (EAlu Instr.ALU_ADD e_sp0' (ELit 8))) with (Sem.alu64 Instr.ALU_ADD (edenot E e_sp0') (edenot E (ELit 8))).
        rewrite u_add64, U_sp0. cbn [edenot]. rewrite !u_lit64a. rewrite (Z.mod_small 8), !Z.mod_small by lia. reflexivity.
      - exact (pre_halted sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS).
      - exact (pre_fs sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS).
      - apply (pre_fds_std sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS). destruct (a_fd cs); [reflexivity|discriminate|discriminate].
      - exact (pre_limit sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS).
      - (* [comment removed for export] *)
        exists (bv_unsigned (ev E 44%nat)). split.
        + exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS 44%nat 1 4194303 H4).
        + pose proof (pre_word_img_at sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS (ELit 0) 0
                        ltac:(cbn [edenot]; rewrite u_lit64a; reflexivity) 0x5e7b30 4 (EVar 44) H5
                        ltac:(cbn [img_lo BOTH]; lia) ltac:(cbn [img_hi BOTH]; lia)) as X.
          cbn [edenot] in X. rewrite Z_to_bv_bv_unsigned. exact X.
      - (* [comment removed for export] *) exact (pre_argblock sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS).
      - (* [comment removed for export] *)
        intros j Hj.
        pose proof (pre_word_at sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS e_sp0' usp U_sp0 8 8 e_p0a H7 ltac:(lia) ltac:(lia)) as X.
        assert (Hrom : forall k, (k < 8)%nat -> seg_rom BSEGS (Z_to_bv 64 (usp + 8 + Z.of_nat k)) = None).
        { intros k Hk. apply (seg_rom_off_hull BSEGS BOTH both_in_hull). unfold in_hull. rewrite u_lit64a, Z.mod_small by lia.
          cbn [img_lo img_hi BOTH]. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
        specialize (X Hrom j Hj). rewrite X. do 2 f_equal. f_equal. apply bv_eq.
        unfold e_p0a. cbn [edenot]. rewrite !u_add64, !u_mul64_boot, !u_lit64a, V0, V6, V1, U_v2.
        (first [ pose proof (usp_split) as dR_15; dand3 dR_15 as US B1 B2 | pose proof usp_split as (US & B1 & B2) ]). unfold p0a, argc, envc, usp in *.
        rewrite !(Z.mod_small 32768), !(Z.mod_small 16), !(Z.mod_small 8), !(Z.mod_small 184) by lia.
        rewrite (Z.mod_small (16 * _)), (Z.mod_small (8 * Z.of_nat (length envp))), (Z.mod_small (8 * Z.of_nat (length argv))), (Z.mod_small (32768 * _)) by lia.
        rewrite (Z.mod_small (8 * Z.of_nat (length envp) + _)) by lia.
        rewrite (Z.mod_small (8 * Z.of_nat (length argv) + _)) by lia.
        rewrite (Z.mod_small (32768 * _ + _)) by lia.
        rewrite !(Z.mod_small (_ + 184)) by lia. lia.
      - (* [comment removed for export] *)
        intros Hargc j Hj.
        pose proof (pre_word_at sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS e_sp0' usp U_sp0 16 8 e_p1 H6 ltac:(lia) ltac:(lia)) as X.
        assert (Hrom : forall k, (k < 8)%nat -> seg_rom BSEGS (Z_to_bv 64 (usp + 16 + Z.of_nat k)) = None).
        { intros k Hk. apply (seg_rom_off_hull BSEGS BOTH both_in_hull). unfold in_hull. rewrite u_lit64a, Z.mod_small by lia.
          cbn [img_lo img_hi BOTH]. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
        specialize (X Hrom j Hj). rewrite X. do 2 f_equal. f_equal. apply bv_eq.
        unfold e_p1. cbn [edenot]. rewrite u_mul64_boot, u_sltu64, !u_add64, !u_mul64_boot, !u_lit64a, V0, V6, V1, U_v2, U_v3.
        (first [ pose proof (usp_split) as dR_16; dand3 dR_16 as US B1 B2 | pose proof usp_split as (US & B1 & B2) ]). unfold p1a, p0a, argc, envc, L0, usp in *.
        rewrite (Z.mod_small 1) by lia.
        replace (1 <? Z.of_nat (length argv)) with true by (symmetry; apply Z.ltb_lt; lia).
        rewrite !(Z.mod_small 32768), !(Z.mod_small 16), !(Z.mod_small 8), !(Z.mod_small 185) by lia.
        rewrite (Z.mod_small (16 * _)), (Z.mod_small (8 * Z.of_nat (length envp))), (Z.mod_small (8 * Z.of_nat (length argv))), (Z.mod_small (32768 * _)) by lia.
        rewrite (Z.mod_small (Z.of_nat (length (nth 0 argv [])) + _)) by lia.
        rewrite (Z.mod_small (8 * Z.of_nat (length envp) + _)) by lia.
        rewrite (Z.mod_small (8 * Z.of_nat (length argv) + _)) by lia.
        rewrite (Z.mod_small (32768 * _ + _)) by lia.
        rewrite (Z.mod_small (_ + 185)), Z.mul_1_l by lia. rewrite !(Z.mod_small (_ + 185)), !(Z.mod_small (_ + 1)) by lia. lia.
      - (* [comment removed for export] *)
        intros i Hi.
        pose proof (pre_wr_at sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS e_sp0' usp U_sp0 (-8388608) 8388608 Cstk ltac:(lia) ltac:(lia) ltac:(lia)) as X.
        replace (usp - 8388608 + i) with (usp + -8388608 + i) by lia. apply X; [|lia].
        intros k Hk. apply (find_segment1_none_outside BSEGS (img_lo BOTH) (img_hi BOTH) _ both_segs_in_hull). cbn [img_lo img_hi BOTH]. right. lia.
      - (* [comment removed for export] *)
        intros lo hi a Hin Ha. unfold chk_img_none in Cimg. apply forallb_forall with (x := (lo, hi)) in Cimg; [|exact Hin].
        cbn [fst snd] in Cimg. apply andb_prop in Cimg as [Cimg C3]. apply andb_prop in Cimg as [C1 C2].
        apply Z.leb_le in C2. apply Z.leb_le in C3. cbn [img_lo img_hi BOTH] in C2, C3.
        unfold kimg_covb in C1. apply existsb_exists in C1 as [K [HK HK2]]. destruct K; try discriminate.
        apply andb_prop in HK2 as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
        pose proof (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ CS) _ HK) as KO. cbn [kentry_ok] in KO. (first [ dand3 KO as _ _ KO | destruct KO as (_ & _ & KO) ]).
        rewrite <- (Mr_image sp rdraw argv envp uid hw Hsp Hva cs E FULL model); [apply KO; lia|].
        rewrite u_lit64a, Z.mod_small by lia. cbn [img_lo img_hi BOTH]. lia.
      - (* [comment removed for export] *)
        intros a w v Hin. unfold chk_words in Cw. apply forallb_forall with (x := (a, w, v)) in Cw; [|exact Hin].
        apply andb_prop in Cw as [C1 C2]. apply andb_prop in C2 as [C2 C3]. apply Z.leb_le in C2. apply Z.leb_le in C3.
        pose proof (pre_word_img_at sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS (ELit 0) 0
                      ltac:(cbn [edenot]; rewrite u_lit64a; reflexivity) a w (ELit v) C1 ltac:(lia) ltac:(lia)) as X.
        cbn [edenot] in X. exact X.
      - (* [comment removed for export] *)
        intros a w v Hin j Hj. unfold chk_words in Cx. apply forallb_forall with (x := (a, w, v)) in Cx; [|exact Hin].
        apply andb_prop in Cx as [C1 C2]. apply andb_prop in C2 as [C2 C3]. apply Z.leb_le in C2. apply Z.leb_le in C3.
        cbn [img_hi BOTH] in C2. unfold CEIL in C3.
        pose proof (pre_word_at sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS (ELit 0) 0
                      ltac:(cbn [edenot]; rewrite u_lit64a; reflexivity) a w (ELit v) C1 ltac:(lia) ltac:(lia)) as X.
        cbn [edenot] in X. rewrite Z.add_0_l in X. apply X; [|exact Hj].
        intros k Hk. apply (seg_rom_off_hull BSEGS BOTH both_in_hull). unfold in_hull. rewrite u_lit64a, Z.mod_small by lia.
        cbn [img_lo img_hi BOTH]. apply andb_false_iff. right. apply Z.ltb_ge. lia.
      - (* [comment removed for export] *)
        intros a n Hin i Hi. unfold chk_zero in Cz. apply forallb_forall with (x := (a, n)) in Cz; [|exact Hin].
        cbn [fst snd] in Cz. apply andb_prop in Cz as [C1 C3]. apply andb_prop in C1 as [C1 C2]. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
        pose proof (pre_zero_at sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS (ELit 0) 0
                      ltac:(cbn [edenot]; rewrite u_lit64a; reflexivity) a n C1 ltac:(lia) i Hi) as X.
        rewrite Z.add_0_l in X. exact X.
      - (* [comment removed for export] *)
        intros a n c Hin i Hi. unfold chk_fill in Cf. apply forallb_forall with (x := (a, n, c)) in Cf; [|exact Hin].
        apply andb_prop in Cf as [C1 C3]. apply andb_prop in C1 as [C1 C2]. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
        pose proof (pre_fill_at sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS (ELit 0) 0
                      ltac:(cbn [edenot]; rewrite u_lit64a; reflexivity) a n c C1 ltac:(lia) i Hi) as X.
        rewrite Z.add_0_l in X. exact X.
    Qed.
  End Derive.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Main.
