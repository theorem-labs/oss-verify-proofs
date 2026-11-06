(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Asanjze AsanInit Star5ef Starob1 Star2r0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanxvb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanjze OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Star5ef OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starob1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Star2r0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Boots35.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module Asan7vn.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec AsanAcct Asanhz7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanjze.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanhz7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanjze.
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
  seg_rom ASEGS (Z_to_bv 64 a) = hex_byte_at Asan_seg_bytes_003 (Z.to_N (a - 0xaa000)).
Proof.
  intros a Ha. unfold seg_rom, memory_read.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
  destruct (find_segment ASEGS a (Z.of_N 1)) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht). rewrite asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size Asan_segment_000 Asan_segment_001
           Asan_segment_002 Asan_segment_003] in Hb, Ht; try (exfalso; cbn in Hb, Ht; lia).
    match goal with |- context [seg_readable ?sg] => replace (seg_readable sg) with true by reflexivity end.
    cbn [seg_base seg_bytes Asan_segment_003]. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at].
    rewrite asan_len3. replace (Z.to_N (a - Z.of_N 696320) <? 5636096)%N with true by (symmetry; apply N.ltb_lt; cbn in Hb, Ht; lia).
    change (Z.of_N 696320) with 0xaa000.
    destruct (hex_byte_at Asan_seg_bytes_003 (Z.to_N (a - 0xaa000))); reflexivity.
  - exfalso. apply (find_segment_none_spec _ _ _ Hf Asan_segment_003); [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.

Lemma rw_zero_range : forall lo n, 0xaa000 <= lo -> lo + Z.of_N n <= 0x60a000 ->
  zscanN Asan_seg_bytes_003 64 (Z.to_N (lo - 0xaa000)) n = true ->
  forall a, lo <= a < lo + Z.of_N n -> seg_rom ASEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
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

Lemma zwin_rw3 : Asan672.zwin Asan_seg_bytes_003 (Uint63.of_Z 65536) (Uint63.of_Z 11206656) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma zr_window : forall base n, (32768 <=? base)%N = true -> (base + n <=? 5636096)%N = true ->
  zscanN Asan_seg_bytes_003 64 base n = true.
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
Lemma zr_depot_tab : zscanN Asan_seg_bytes_003 64 (Z.to_N (0x197298 - 0xaa000)) 0x400000 = true.
Proof. apply zr_window; vm_compute; congruence. Qed.
Lemma zr_depot_map1 : zscanN Asan_seg_bytes_003 64 (Z.to_N (0x5972a8 - 0xaa000)) 0x40000 = true.
Proof. apply zr_window; vm_compute; congruence. Qed.
Lemma zr_ia_inst : zscanN Asan_seg_bytes_003 64 (Z.to_N (0xb65c0 - 0xaa000)) 0x81040 = true.
Proof. apply zr_window; vm_compute; congruence. Qed.
Lemma zr_hooks : zscanN Asan_seg_bytes_003 64 (Z.to_N (0x146e80 - 0xaa000)) 80 = true.
Proof. apply zr_window; vm_compute; congruence. Qed.
Lemma zr_instance : zscanN Asan_seg_bytes_003 64 (Z.to_N (0xb1d58 - 0xaa000)) 3632 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma img0_depot_tab : forall a, 0x197298 <= a < 0x197298 + 0x400000 -> seg_rom ASEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof. intros a Ha. apply (rw_zero_range 0x197298 0x400000%N); [lia|cbn; lia| exact zr_depot_tab| cbn; lia]. Qed.
Lemma img0_depot_map1 : forall a, 0x5972a8 <= a < 0x5972a8 + 0x40000 -> seg_rom ASEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof. intros a Ha. apply (rw_zero_range 0x5972a8 0x40000%N); [lia|cbn; lia| exact zr_depot_map1| cbn; lia]. Qed.
Lemma img0_ia_inst : forall a, 0xb65c0 <= a < 0xb65c0 + 0x81040 -> seg_rom ASEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof. intros a Ha. apply (rw_zero_range 0xb65c0 0x81040%N); [lia|cbn; lia| exact zr_ia_inst| cbn; lia]. Qed.
Lemma img0_hooks : forall a, 0x146e80 <= a < 0x146e80 + 80 -> seg_rom ASEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof. intros a Ha. apply (rw_zero_range 0x146e80 80%N); [lia|cbn; lia| exact zr_hooks| cbn; lia]. Qed.
Lemma img0_instance : forall a, 0xb1d58 <= a < 0xb1d58 + 3632 -> seg_rom ASEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof. intros a Ha. apply (rw_zero_range 0xb1d58 3632%N); [lia|cbn; lia| exact zr_instance| cbn; lia]. Qed.
End Asan7vn.

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
  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  #[local] Notation LIM := (@AsanInit.blim BL).

  Variable cs : acs.
  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis CS : cs_ok ASEGS ASAN LIM SINV argH fs E cs R FULL model.

  #[local] Notation MR := (Mr ASAN argH E cs model FULL).

  (* [comment removed for export] *)
  Definition khas (K : kentry) : bool := existsb (kentry_eqb K) (kn cs).

  Lemma khas_ok : forall K, khas K = true -> kentry_ok ASEGS E MR K.
  Proof.
    intros K H. unfold khas in H. apply existsb_exists in H as [k [Hin Heq]]. apply kentry_eqb_eq in Heq. subst k.
    exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ CS) _ Hin).
  Qed.

  (* [comment removed for export] *)
  Lemma pre_top : alloc_top (m_vmmaps model) + 8388608 = bv_unsigned sp.
  Proof.
    rewrite (co_top _ _ _ _ _ _ _ _ _ _ _ CS).
    exact (SINV0_sp APH sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit (SINV0 APH sp rdraw brk0 argv envp uid hw) (fun E M H => H)
             E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ CS)).
  Qed.
  Lemma pre_top_ceil : CEIL <= alloc_top (m_vmmaps model).
  Proof. pose proof pre_top. pose proof Hsp as (H1 & _). unfold sp_window_lo in H1. unfold CEIL. lia. Qed.

  (* [comment removed for export] *)
  Lemma Mr_some : forall a b, MR a = Some b -> FULL a = Some b.
  Proof. intros a b H. unfold Mr, mrestrict in H. destruct (hid ASAN argH E cs model a); [discriminate|exact H]. Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma hid_image : forall a : word, img_lo ASAN <= bv_unsigned a < img_hi ASAN -> hid ASAN argH E cs model a = false.
  Proof.
    intros a Ha. unfold hid. destruct (argH0 APH sp rdraw argv envp uid hw E a) eqn:HA.
    - exfalso. pose proof (argH0_high APH sp rdraw argv envp uid hw Hsp Hva E a HA) as X. unfold CEIL in X. cbn [img_hi ASAN] in Ha. lia.
    - cbn [orb]. unfold vis. unfold in_hull. destruct Ha as [H1 H2].
      rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2). reflexivity.
  Qed.
  Lemma Mr_image : forall a : word, img_lo ASAN <= bv_unsigned a < img_hi ASAN -> MR a = FULL a.
  Proof. intros a Ha. unfold Mr, mrestrict. rewrite (hid_image a Ha). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rdn_ext : forall (m1 m2 : word -> option byte) n (a : word),
    (forall j, (j < n)%nat -> m1 (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = m2 (Z_to_bv 64 (bv_unsigned a + Z.of_nat j))) ->
    rdn ASEGS m1 a n = rdn ASEGS m2 a n.
  Proof.
    intros m1 m2 n. induction n as [|n IH]; intros a Heq; [reflexivity|].
    cbn [rdn]. pose proof (Heq 0%nat ltac:(lia)) as H0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
    rewrite (IH (a + 1)%bv); [reflexivity|].
    intros j Hj. rewrite !u_succ_shift. replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia. apply Heq. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_bytes : forall (m : word -> option byte) n (a : word) bs,
    (forall j, (j < n)%nat -> seg_rom ASEGS (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = None) ->
    rdn ASEGS m a n = Some bs ->
    forall j, (j < n)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
  Proof.
    intros m n. induction n as [|n IH]; intros a bs Hrom Hr j Hj; [lia|].
    cbn [rdn] in Hr. pose proof (Hrom 0%nat ltac:(lia)) as R0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in R0.
    destruct (m a) as [b|] eqn:Hm.
    - destruct (rdn ASEGS m (a + 1)%bv n) as [rest|] eqn:Hr'; [|discriminate]. injection Hr as <-.
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
    store_ok ASEGS m a n = true -> bv_unsigned a + Z.of_nat n <= 2^64 ->
    forall j, (j < n)%nat -> find_segment ASEGS (bv_unsigned a + Z.of_nat j) 1 = None -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None.
  Proof.
    intros m n. induction n as [|n IH]; intros a H Hn j Hj Hseg; [lia|].
    cbn [store_ok] in H. destruct (wview ASEGS m a) as [b|] eqn:Ew; [|discriminate].
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
      (forall j, (j < w)%nat -> seg_rom ASEGS (Z_to_bv 64 (B + off + Z.of_nat j)) = None) ->
      forall j, (j < w)%nat -> FULL (Z_to_bv 64 (B + off + Z.of_nat j)) = Some (nth j (word_to_le_bytes w (edenot E ve)) (Z_to_bv 8 0)).
    Proof.
      intros off w ve H Hlo Hhi Hrom j Hj. apply khas_ok in H. (first [ dand3 H as Hw _ Hr | destruct H as (Hw & _ & Hr) ]).
      rewrite adenot_at in Hr by lia. apply Mr_some.
      pose proof (rdn_bytes MR w (Z_to_bv 64 (B + off)) _ ltac:(intros k Hk; rewrite u_lit64a, Z.mod_small by lia; apply Hrom; exact Hk) Hr j Hj) as X.
      rewrite u_lit64a, Z.mod_small in X by lia. exact X.
    Qed.

    (* [comment removed for export] *)
    Lemma pre_word_img_at : forall off w ve, khas (KWord (SA b off) w ve) = true ->
      img_lo ASAN <= B + off -> B + off + Z.of_nat w <= img_hi ASAN ->
      rdn ASEGS FULL (Z_to_bv 64 (B + off)) w = Some (word_to_le_bytes w (edenot E ve)).
    Proof.
      intros off w ve H Hlo Hhi. apply khas_ok in H. (first [ dand3 H as Hw _ Hr | destruct H as (Hw & _ & Hr) ]).
      cbn [img_lo img_hi ASAN] in Hlo, Hhi.
      rewrite adenot_at in Hr by lia.
      rewrite <- (rdn_ext MR FULL w (Z_to_bv 64 (B + off))); [exact Hr|].
      intros j Hj. apply Mr_image. cbn [img_lo img_hi ASAN]. rewrite (u_lit64a (B + off)), (Z.mod_small (B + off)) by lia.
      rewrite u_lit64a, Z.mod_small by lia. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma pre_wr_at : forall off n, khas (KWr (SA b off) (ELit n)) = true ->
      0 <= B + off -> 0 <= n < 2^64 -> B + off + n <= 2^64 ->
      (forall i, 0 <= i < n -> find_segment ASEGS (B + off + i) 1 = None) ->
      forall i, 0 <= i < n -> FULL (Z_to_bv 64 (B + off + i)) <> None.
    Proof.
      intros off n H Hlo Hn Hhi Hseg i Hi. apply khas_ok in H. destruct H as [_ H].
      rewrite estart_at, elenZ_lit in H by lia.
      specialize (H i 1%nat ltac:(lia) ltac:(lia)).
      intros X. apply (store_ok_present MR 1 (Z_to_bv 64 (B + off + i)) H ltac:(rewrite u_lit64a, Z.mod_small; lia) 0%nat ltac:(lia)).
      - rewrite u_lit64a, Z.mod_small by lia. rewrite Z.add_0_r. apply Hseg. lia.
      - rewrite u_lit64a, Z.mod_small, Nat2Z.inj_0, Z.add_0_r by lia.
        unfold Mr, mrestrict. destruct (hid ASAN argH E cs model (Z_to_bv 64 (B + off + i))); [reflexivity|exact X].
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

  Lemma pre_ev_lt9 : forall n, (n < NX0)%nat -> ev E n = ev (E0 APH sp rdraw brk0 argv envp uid hw) n.
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
  Lemma pre_argblock : forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> FULL a = wrap_mem APH sp argv envp uid hw rdraw a.
  Proof. destruct pre_sinv as [_ H]. exact H. Qed.

  (* [comment removed for export] *)
  Lemma pre_in_maps : forall m, In m (a_maps cs) -> is_fog m = false ->
    In (amap_den E m) (vm_maps (m_vmmaps model)).
  Proof. intros m Hin Hf. exact (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ CS) Hin Hf). Qed.

  Lemma pre_limit : vm_limit (m_vmmaps model) = LIM.
  Proof. exact (co_limit _ _ _ _ _ _ _ _ _ _ _ CS). Qed.
  (* [comment removed for export] *)
  Lemma pre_res : vm_reserved (m_vmmaps model) = segments_reserved ASEGS.
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
    z < CEIL -> img_hi ASAN <= z ->
    in_vis E cs z = false -> in_sh ASAN E cs z = false -> in_ghost E cs z = false ->
    FULL (Z_to_bv 64 z) = Some (Z_to_bv 8 0).
  Proof.
    intros mz z Hmin Hnf Hkind Hz Hceil Himg Hnv Hns Hng.
    pose proof (u64_range (edenot E (am_base mz))) as Rb.
    assert (Rz : 0 <= z < 2^64) by (unfold uE in Hz; unfold CEIL in Hceil; lia).
    set (a := Z_to_bv 64 z). assert (Ua : bv_unsigned a = z) by (unfold a; rewrite u_lit64a; apply Z.mod_small; exact Rz).
    assert (Hm1 : in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true).
    { eapply in_ivs_maps_match; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ CS) | exact Hmin | exact Hnf |]. rewrite Ua. unfold uE in Hz. exact Hz. }
    destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ CS) mz Hmin Hkind a ltac:(rewrite Ua; unfold uE in Hz; exact Hz)) as [Hna Hlz].
    assert (Hargh : argH0 APH sp rdraw argv envp uid hw E a = false).
    { destruct (argH0 APH sp rdraw argv envp uid hw E a) eqn:Ha; [|reflexivity]. pose proof (argH0_high APH sp rdraw argv envp uid hw Hsp Hva E a Ha). lia. }
    assert (Hhid : hid ASAN (argH0 APH sp rdraw argv envp uid hw) E cs model a = true).
    { unfold hid. rewrite Hargh. cbn [orb]. apply negb_true_iff. unfold vis.
      rewrite Hm1, Hna, Hlz. cbn [negb andb]. unfold in_allow. rewrite Ua, Hnv, Hns. cbn [orb].
      unfold in_hull. replace (z <? img_hi ASAN) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
      pose proof pre_top_ceil. replace (alloc_top (m_vmmaps model) <=? z) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    rewrite <- Ua in Hng. exact (co_zero _ _ _ _ _ _ _ _ _ _ _ CS a Hhid Hm1 Hna Hlz Hng).
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mb (a : Z) : option byte :=
    match FULL (Z_to_bv 64 a) with Some b => Some b | None => seg_rom ASEGS (Z_to_bv 64 a) end.

  (* [comment removed for export] *)
  Lemma rdn_mbytes : forall (m : word -> option byte) n (a : word) bs,
    rdn ASEGS m a n = Some bs ->
    forall j, (j < n)%nat ->
      match m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) with Some b => Some b | None => seg_rom ASEGS (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) end
      = Some (nth j bs (Z_to_bv 8 0)).
  Proof.
    intros m n. induction n as [|n IH]; intros a bs Hr j Hj; [lia|].
    cbn [rdn] in Hr.
    destruct (match m a with Some b => Some b | None => seg_rom ASEGS a end) as [b|] eqn:Hm; [|discriminate].
    destruct (rdn ASEGS m (a + 1)%bv n) as [rest|] eqn:Hr'; [|discriminate]. injection Hr as <-.
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

  Lemma kbyte_sound : forall k a b, Forall (kentry_ok ASEGS E MR) k -> kbyte k a = Some b -> 0 <= a < 2^64 -> mb a = Some b.
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
      destruct (hid ASAN argH E cs model (Z_to_bv 64 a)) eqn:Hh.
      + (* [comment removed for export] *)
        destruct (seg_rom ASEGS (Z_to_bv 64 a)) as [rb|] eqn:Hrom; [|discriminate].
        exfalso. unfold seg_rom in Hrom. unfold memory_read in Hrom.
        destruct (find_segment ASEGS (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [seg|] eqn:Hf; [|discriminate].
        apply find_segment_some_spec in Hf as (Hin & Hb1 & Hb2).
        pose proof (proj1 (forallb_forall _ _) asan_segs_in_hull seg Hin) as SB. apply andb_true_iff in SB as [SB1 SB2].
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
  Lemma kimg_mb : forall lo hi a, khas (KImg lo hi) = true -> lo <= a < hi -> img_lo ASAN <= lo -> hi <= img_hi ASAN ->
    FULL (Z_to_bv 64 a) = None /\ mb a = seg_rom ASEGS (Z_to_bv 64 a).
  Proof.
    intros lo hi a H Ha Hlo Hhi. apply khas_ok in H. (first [ dand3 H as _ _ H | destruct H as (_ & _ & H) ]). specialize (H a Ha).
    rewrite Mr_image in H by (rewrite u_lit64a, Z.mod_small; cbn [img_lo img_hi ASAN] in *; lia).
    split; [exact H|]. unfold mb. rewrite H. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition kimg_cov1 (k : list kentry) (a : Z) : bool :=
    existsb (fun K => match K with KImg lo hi => (lo <=? a) && (a <? hi) && (img_lo ASAN <=? lo) && (hi <=? img_hi ASAN) | _ => false end)%bool k.
  Definition byte_okb (k : list kentry) (a : Z) (b : byte) : bool :=
    match kbyte k a with
    | Some b' => bv_eqb b' b
    | None => kimg_cov1 k a && match seg_rom ASEGS (Z_to_bv 64 a) with Some b' => bv_eqb b' b | None => false end
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
      | KImg lo hi => (lo <=? a) && (a + n <=? hi) && (img_lo ASAN <=? lo) && (hi <=? img_hi ASAN)
      | _ => false end)%bool k.
  Fixpoint bytes_eqb (xs ys : list byte) : bool :=
    match xs, ys with [], [] => true | x :: xs', y :: ys' => bv_eqb x y && bytes_eqb xs' ys' | _, _ => false end%bool.
  Definition cell_okb (k : list kentry) (a : Z) (bs : list byte) : bool :=
    let n := Z.of_nat (length bs) in
    if kzero_covr k a n then forallb (fun b => bv_eqb b (Z_to_bv 8 0)) bs
    else if kimg_covr k a n then
      match rdn ASEGS (fun _ => None) (Z_to_bv 64 a) (length bs) with Some bs' => bytes_eqb bs' bs | None => false end
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
      destruct (seg_rom ASEGS (Z_to_bv 64 a)) as [b'|]; [|discriminate]. apply bv_eqb_eq8 in HR. subst b'. reflexivity.
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
        destruct (rdn ASEGS (fun _ => None) (Z_to_bv 64 a) (length bs)) as [bs'|] eqn:RD; [|discriminate].
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
    khas (KImg lo' hi') = true -> lo' <= lo -> hi <= hi' -> img_lo ASAN <= lo' -> hi' <= img_hi ASAN ->
    (forall a, lo <= a < hi -> seg_rom ASEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
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
  [(0x10000, 0xab078); (0xab088, 0xab090); (0xab094, 0xb1d00); (0xb1d09, 0xb1d58); (0xb1d70, 0xb1d78); (0xb1d84, 0xb1d88); (0xb1d91, 0xb1d98); (0xb1dc0, 0xb2000); (0xb2004, 0xb2070); (0xb2088, 0xb20c8); (0xb20ca, 0xb2b78); (0xb2b85, 0xb2bb8); (0xb2bcd, 0xb2bd0); (0xb2be1, 0xb2be4); (0xb2bf5, 0xb2bf8); (0xb2c13, 0xb2c14); (0xb2c19, 0xb2c1c); (0xb2c2c, 0xb2c30); (0xb2c31, 0xb2c38); (0xb2c58, 0xb2c68); (0xb2c78, 0xb2c98); (0xb2cb0, 0xb2cb8); (0xb3f68, 0xb4bf8); (0xb4bfb, 0xb4bfc); (0xb4c10, 0xb4c18); (0xb4c1d, 0xb4c20); (0xb4c21, 0xb4c24); (0xb4c28, 0xb53b8); (0xb53c4, 0xb6098); (0xb609c, 0xb60a0); (0xb60a8, 0xb60b8); (0xb60b9, 0xb60bc); (0xb60c0, 0xb6130); (0xb6140, 0xb6400); (0xb6408, 0xb6440); (0xb644c, 0xb6450); (0xb646d, 0xb64a8); (0xb64a9, 0xb64b0); (0xb64b1, 0xb64b8); (0xb64d0, 0xb64d8); (0xb652c, 0xb6530); (0xb65bc, 0x137608); (0x137620, 0x137621); (0x137622, 0x144e50); (0x144e5c, 0x144e60); (0x144e68, 0x144e80); (0x145e7f, 0x145e80); (0x146e7f, 0x146ee0); (0x146ee4, 0x146ee8); (0x147008, 0x1470d0); (0x1470d8, 0x1470f8); (0x147100, 0x147110); (0x147128, 0x147148); (0x147149, 0x147258); (0x147259, 0x187288); (0x1872a8, 0x25d7c4); (0x25d7c8, 0x524a04); (0x524a08, 0x597298); (0x59729c, 0x5972a0); (0x5972a4, 0x5972a8); (0x5972b0, 0x5d7780); (0x5d7781, 0x5d7784); (0x5d7797, 0x5d7798); (0x5d779c, 0x5d77a0); (0x5d77ac, 0x5d7940); (0x5d7948, 0x5d7980); (0x5d798c, 0x5d7990); (0x5d79ce, 0x5d79e8); (0x5d79e9, 0x5d79f0); (0x5d79f4, 0x5d79f8); (0x5d79fa, 0x5d7a00); (0x5d7a0a, 0x5e7a80); (0x5e7a82, 0x5e7ac0); (0x5e7ac2, 0x5e8308); (0x5e8334, 0x5e8338); (0x5e833c, 0x5e8342); (0x5e8343, 0x5e8380); (0x5e8390, 0x5e83a8); (0x5e83b0, 0x5e83c8); (0x5e83e8, 0x5e83f8); (0x5e8408, 0x6083f0); (0x608420, 0x608430); (0x608434, 0x608438); (0x608440, 0x608448); (0x608450, 0x608548); (0x608550, 0x608658); (0x608669, 0x608670); (0x6086a0, 0x6086d0); (0x6086d8, 0x6086e8); (0x6086f8, 0x608700); (0x608738, 0x608748); (0x608750, 0x6087b0); (0x6087b8, 0x6087d0); (0x6087d8, 0x6087f0); (0x6087f8, 0x6088c8); (0x6088d0, 0x608930); (0x608938, 0x608950); (0x608958, 0x608970); (0x608978, 0x608a78); (0x608a79, 0x608a80); (0x608a88, 0x609330); (0x609338, 0x609340); (0x609348, 0x609740); (0x609744, 0x609748); (0x60974c, 0x609780); (0x609788, 0x60a000)].
Definition IMG_WORDS : list (Z * nat * Z) :=
  [(0xb2c70, 8%nat, 0x0); (0xb2c30, 1%nat, 0x1); (0xb1d08, 1%nat, 0x1); (0xb1d00, 8%nat, 0x1); (0xb2c38, 8%nat, 0x103); (0x5e7ac0, 1%nat, 0x1); (0xb2ca0, 4%nat, 0x4); (0x5e7a81, 1%nat, 0x1); (0x5e7a80, 1%nat, 0x1); (0x5e7ac1, 1%nat, 0x1); (0xb2ca4, 4%nat, 0x0); (0xb2ca8, 4%nat, 0x80); (0xb2cac, 4%nat, 0x0); (0xb2c68, 8%nat, 0xb2c98); (0x1872a4, 1%nat, 0x0); (0x187290, 8%nat, 0x800000); (0x1872a5, 3%nat, 0x0); (0x5972a0, 1%nat, 0x0); (0x5972a1, 3%nat, 0x0); (0x597298, 4%nat, 0x1); (0xb609a, 1%nat, 0x0); (0xb6400, 8%nat, 0xb6440); (0xb6460, 8%nat, 0x0); (0xb64a8, 1%nat, 0x1); (0xb6458, 8%nat, 0x0); (0xb6450, 8%nat, 0x0); (0xb6448, 4%nat, 0x5); (0xb6440, 8%nat, 0xab040); (0x5d79f0, 1%nat, 0x0); (0x5d79f1, 1%nat, 0x1); (0x5d7940, 8%nat, 0x5d7980); (0x5d79a0, 8%nat, 0x0); (0x5d79e8, 1%nat, 0x1); (0x5d7998, 8%nat, 0x0); (0x5d7990, 8%nat, 0x0); (0x5d7988, 4%nat, 0x26); (0x5d7980, 8%nat, 0xad610); (0x5d79f2, 2%nat, 0x0); (0x6088c8, 8%nat, 0xa); (0x608930, 8%nat, 0x2); (0x608950, 8%nat, 0x2); (0x608970, 8%nat, 0x2); (0x6086f4, 4%nat, 0x1); (0x608a78, 1%nat, 0x1); (0x608708, 8%nat, 0x61); (0x608710, 8%nat, 0x0); (0x6086f0, 4%nat, 0x1); (0xb6530, 8%nat, 0x0); (0xb6558, 8%nat, 0x1); (0x147148, 1%nat, 0x1); (0xb2000, 1%nat, 0x0); (0xb2001, 3%nat, 0x0); (0x1470f8, 8%nat, 0x1); (0x5e8342, 1%nat, 0x1); (0xb6540, 8%nat, 0x1); (0xb6550, 8%nat, 0x1); (0xb6548, 8%nat, 0x1); (0xb6570, 8%nat, 0x1); (0xb6568, 8%nat, 0x1000); (0xb64c8, 8%nat, 0x0); (0xb6510, 4%nat, 0x0); (0xb6508, 4%nat, 0x0); (0xb6500, 8%nat, 0x0); (0xb64f8, 8%nat, 0x0); (0xb64c0, 8%nat, 0xb64e8); (0xb64b0, 1%nat, 0x1); (0xb64f4, 4%nat, 0x0); (0xb64f0, 4%nat, 0x0); (0xb64e8, 8%nat, 0x0); (0xb6514, 4%nat, 0x0); (0xb650c, 4%nat, 0x0); (0xb64b8, 8%nat, 0xb6518); (0xb6598, 8%nat, 0x0); (0xb6590, 8%nat, 0x0); (0xb6588, 8%nat, 0x0); (0xb6580, 8%nat, 0x0); (0xb6578, 8%nat, 0x0); (0xb65b8, 4%nat, 0x0); (0xb65b0, 8%nat, 0x0); (0xb65a8, 8%nat, 0x0); (0xb65a0, 8%nat, 0x0); (0xb653c, 4%nat, 0x0); (0xb6538, 4%nat, 0x0); (0xb6528, 4%nat, 0x0); (0xb6520, 8%nat, 0xffffffffffffffff); (0xb6518, 8%nat, 0x641e8); (0x147120, 8%nat, 0x76378); (0x608430, 4%nat, 0x1); (0x608548, 8%nat, 0x76378); (0x608448, 8%nat, 0x98958); (0x608438, 8%nat, 0x608440); (0x147258, 1%nat, 0x0); (0xb6098, 1%nat, 0x1); (0xb6099, 1%nat, 0x1); (0xb2b78, 8%nat, 0x10000000000); (0xb2b82, 2%nat, 0x800); (0xb2b80, 2%nat, 0x10); (0xb2b84, 1%nat, 0x1); (0xb20c9, 1%nat, 0x0); (0xb20c8, 1%nat, 0x0); (0xb2080, 8%nat, 0x100000); (0xb2078, 8%nat, 0xe666661); (0xb2070, 8%nat, 0x10000000); (0xb1db8, 8%nat, 0x19805); (0xb1db0, 8%nat, 0x800000); (0xb1d98, 8%nat, 0x1000); (0xb1d80, 4%nat, 0xffffffffffffffff); (0xb6138, 8%nat, 0x1000); (0xb6130, 8%nat, 0x1); (0xb1d68, 8%nat, 0x16e32); (0xb1d60, 8%nat, 0x2000011000); (0xb1d90, 1%nat, 0x0); (0x137621, 1%nat, 0x1); (0x609748, 4%nat, 0x0); (0x609340, 8%nat, 0x5af7c); (0x609740, 4%nat, 0x0); (0xb4c24, 4%nat, 0x0); (0x5e8380, 8%nat, 0x609780); (0xb4c20, 1%nat, 0x1); (0xb53b8, 8%nat, 0x7fff8000); (0xb4bfa, 1%nat, 0x1); (0xb4bf8, 1%nat, 0x1); (0xb4bfc, 4%nat, 0x12b); (0xb4c00, 8%nat, 0xb4c08); (0xb4bf9, 1%nat, 0x1); (0x137618, 8%nat, 0x602dc); (0xab078, 8%nat, 0x8); (0xb53c0, 4%nat, 0x1); (0x146ee0, 1%nat, 0x0); (0xab090, 4%nat, 0x2); (0x146ee1, 3%nat, 0x0); (0x1470d0, 8%nat, 0x5b180); (0x147110, 8%nat, 0x60250); (0x147118, 8%nat, 0x60168); (0xb60a0, 8%nat, 0x7fffffffffff); (0xb60bc, 4%nat, 0x1e); (0xb4c1c, 1%nat, 0x1); (0xb4c18, 4%nat, 0x2); (0xb2c06, 1%nat, 0x1); (0x146ee8, 8%nat, 0x1); (0x146ef0, 8%nat, 0x0); (0x146ef8, 8%nat, 0x0); (0x146f00, 8%nat, 0x140a1); (0x146f08, 8%nat, 0x1e00010000); (0x146f10, 8%nat, 0x0); (0x146f18, 8%nat, 0x0); (0x146f20, 8%nat, 0x0); (0x146f28, 8%nat, 0x0); (0x146f30, 8%nat, 0x10101000101); (0x146f38, 8%nat, 0x100000000); (0x146f40, 8%nat, 0x0); (0x146f48, 8%nat, 0x0); (0x146f50, 8%nat, 0x0); (0x146f58, 8%nat, 0x10001); (0x146f60, 8%nat, 0xffffffffffffffff); (0x146f68, 8%nat, 0x118c7); (0x146f70, 8%nat, 0x100); (0x146f78, 8%nat, 0x0); (0x146f80, 8%nat, 0x0); (0x146f88, 8%nat, 0x0); (0x146f90, 8%nat, 0x0); (0x146f98, 8%nat, 0xffffffff00000000); (0x146fa0, 8%nat, 0x1); (0x146fa8, 8%nat, 0x143fd); (0x146fb0, 8%nat, 0x140a1); (0x146fb8, 8%nat, 0x140a1); (0x146fc0, 8%nat, 0x10101000100); (0x146fc8, 8%nat, 0x0); (0x146fd0, 8%nat, 0x1e205); (0x146fd8, 8%nat, 0x101000100000000); (0x146fe0, 8%nat, 0x101010101010101); (0x146fe8, 8%nat, 0x1010101); (0x146ff0, 8%nat, 0x10100000001); (0x146ff8, 8%nat, 0x19077); (0x147000, 8%nat, 0x1000000000100); (0xb2bc0, 4%nat, 0x400); (0xb2bbc, 4%nat, 0x100); (0x144e58, 4%nat, 0x0); (0x5d7a08, 2%nat, 0x0); (0x5d7a00, 8%nat, 0x140a1); (0x5d79f8, 2%nat, 0x0); (0x5d77a8, 4%nat, 0x1); (0x5d7790, 4%nat, 0x101); (0x5d7788, 8%nat, 0x101010100000000); (0x5d7784, 4%nat, 0x0); (0x5d7780, 1%nat, 0x0); (0x5d77a0, 8%nat, 0x140a1); (0x5d7798, 4%nat, 0x1); (0x5d7796, 1%nat, 0x0); (0x5d7794, 2%nat, 0x0); (0xb2c12, 1%nat, 0x0); (0xb2bcc, 1%nat, 0x0); (0xb2c20, 8%nat, 0x140a1); (0xb2c1c, 4%nat, 0x2); (0xb2c18, 1%nat, 0x1); (0xb2c14, 4%nat, 0x0); (0xb2c10, 2%nat, 0x1); (0xb2c08, 8%nat, 0x101010101000001); (0xb2c00, 6%nat, 0x100000000); (0xb2c07, 1%nat, 0x0); (0xb2be4, 4%nat, 0x1000); (0xb2be0, 1%nat, 0x0); (0xb2bd8, 8%nat, 0x1400000010); (0xb2bd0, 8%nat, 0x101010000000001); (0xb2bc8, 4%nat, 0x800); (0xb2bf8, 8%nat, 0x0); (0xb2bf4, 1%nat, 0x1); (0xb2bf0, 4%nat, 0x55); (0xb2be8, 8%nat, 0xbe00000000); (0xb2bc4, 4%nat, 0x10); (0xb2bb8, 4%nat, 0xffffffff); (0xb2c28, 4%nat, 0x10101); (0x144e60, 8%nat, 0x1000); (0xb60b8, 1%nat, 0x1); (0xab080, 8%nat, 0x20bc5); (0xb609b, 1%nat, 0x0); (0x5e8b18, 8%nat, 0x0); (0x608419, 1%nat, 0x0); (0x5e8328, 8%nat, 0x0); (0x5e8320, 8%nat, 0x5e8310); (0x5e8318, 8%nat, 0x5e8310); (0x5e8388, 8%nat, 0x5e8388); (0x5e83a8, 8%nat, 0x6086a0); (0x5e8338, 4%nat, 0x2); (0x608668, 1%nat, 0x1); (0x5e8310, 8%nat, 0x5e8310); (0x5e83d0, 8%nat, 0x5e83f8); (0x5e83f8, 8%nat, 0x1); (0x5e8400, 8%nat, 0x5e8bd8); (0x608688, 8%nat, 0x8); (0x608680, 8%nat, 0xf8); (0x608410, 8%nat, 0x0); (0x608400, 8%nat, 0x18); (0x608690, 8%nat, 0x1); (0x608678, 8%nat, 0x6083e8); (0x608408, 8%nat, 0x8); (0x6083f8, 8%nat, 0x0); (0x6083f0, 8%nat, 0xa79e8); (0x608698, 8%nat, 0x1000)].
Definition EXT_WORDS : list (Z * nat * Z) :=
  [(0x7fffc89d, 1%nat, 0x5); (0x7fffc895, 1%nat, 0x4); (0x7fffc891, 1%nat, 0x7); (0x7fffc88a, 1%nat, 0x1); (0x7fffc879, 1%nat, 0x2); (0x7fffc870, 1%nat, 0x6); (0x7fffc869, 1%nat, 0x7); (0x7fffc863, 1%nat, 0x6); (0x7fffc858, 1%nat, 0x2); (0x7fffc849, 1%nat, 0x6); (0x7fffc842, 1%nat, 0x3); (0x7fffc83d, 1%nat, 0x1); (0x7fffc836, 1%nat, 0x7); (0x7fffc82a, 1%nat, 0x3); (0x7fffc820, 1%nat, 0x6); (0x7fffc81c, 1%nat, 0x5); (0x7fffc818, 1%nat, 0x5); (0x7fffc814, 1%nat, 0x7); (0x7fffc810, 1%nat, 0x7); (0x7fffc80c, 1%nat, 0x6); (0x7fffc806, 1%nat, 0x2); (0x7fffc7f9, 1%nat, 0x4); (0x7fffc7f1, 1%nat, 0x1); (0x7fffc7ed, 1%nat, 0x5); (0x7fffc7e4, 1%nat, 0x7); (0x7fffc7d5, 1%nat, 0x3); (0x7fffc7c8, 1%nat, 0x5); (0x7fffc7bc, 1%nat, 0x6); (0x7fffc7b5, 1%nat, 0x7); (0x7fffc7ac, 1%nat, 0x2); (0x7fffc7a5, 1%nat, 0x7); (0x7fffc7a1, 1%nat, 0x1); (0x7fffc79c, 1%nat, 0x5); (0x7fffc794, 1%nat, 0x7); (0x7fffc78a, 1%nat, 0x2); (0x7fffc785, 1%nat, 0x1); (0x7fffc780, 1%nat, 0x5); (0x7fffc77c, 1%nat, 0x6); (0x7fffc778, 1%nat, 0x4); (0x7fffc774, 1%nat, 0x7); (0x7fffc770, 1%nat, 0x7); (0x7fffc76c, 1%nat, 0x4); (0x7fffc768, 1%nat, 0x7); (0x7fffc762, 1%nat, 0x2); (0x7fffc758, 1%nat, 0x1); (0x7fffc74b, 1%nat, 0x4); (0x7fffc742, 1%nat, 0x7); (0x7fffc73d, 1%nat, 0x3); (0x7fffc738, 1%nat, 0x3); (0x7fffc72f, 1%nat, 0x6); (0x7fffc727, 1%nat, 0x3); (0x7fffc721, 1%nat, 0x6); (0x7fffc71b, 1%nat, 0x2); (0x7fffc715, 1%nat, 0x5); (0x7fffc711, 1%nat, 0x1); (0x7fffc70a, 1%nat, 0x7); (0x7fffc704, 1%nat, 0x7); (0x7fffc6fe, 1%nat, 0x2); (0x7fffc6f9, 1%nat, 0x3); (0x7fffc6f3, 1%nat, 0x2); (0x7fffc6e8, 1%nat, 0x1); (0x7fffc6d0, 1%nat, 0x4); (0x7fffc6c9, 1%nat, 0x4); (0x7fffc6c5, 1%nat, 0x7); (0x7fffc6bf, 1%nat, 0x2); (0x7fffc6b9, 1%nat, 0x4); (0x7fffc6ae, 1%nat, 0x5); (0x7fffc6a6, 1%nat, 0x7); (0x7fffc69c, 1%nat, 0x5); (0x7fffc695, 1%nat, 0x4); (0x7fffc68c, 1%nat, 0x7); (0x7fffc682, 1%nat, 0x4); (0x7fffc67b, 1%nat, 0x4); (0x7fffc675, 1%nat, 0x4); (0x7fffc66c, 1%nat, 0x7); (0x7fffc662, 1%nat, 0x5); (0x7fffc659, 1%nat, 0x6); (0x7fffc655, 1%nat, 0x5); (0x7fffc648, 1%nat, 0x7); (0x7fffc641, 1%nat, 0x3); (0x7fffc63a, 1%nat, 0x5); (0x7fffc631, 1%nat, 0x6); (0x7fffc62d, 1%nat, 0x1); (0x7fffc629, 1%nat, 0x2); (0x7fffc624, 1%nat, 0x4); (0x7fffc619, 1%nat, 0x7); (0x7fffc611, 1%nat, 0x5); (0x7fffc608, 1%nat, 0x4); (0x7fffc605, 1%nat, 0x2); (0x7fffc601, 1%nat, 0x2); (0x7fffc5fd, 1%nat, 0x3); (0x7fffc5f6, 1%nat, 0x1); (0x7fffc5e9, 1%nat, 0x1); (0x7fffc5e2, 1%nat, 0x2); (0x7fffc5d5, 1%nat, 0x3); (0x7fffc5d1, 1%nat, 0x2); (0x7fffc5cd, 1%nat, 0x1); (0x7fffc5c8, 1%nat, 0x6); (0x7fffc5b6, 1%nat, 0x2); (0x7fffc5ae, 1%nat, 0x3); (0x7fffc5a8, 1%nat, 0x1); (0x7fffc5a4, 1%nat, 0x6); (0x7fffc59f, 1%nat, 0x3); (0x7fffc599, 1%nat, 0x6); (0x7fffc58d, 1%nat, 0x2); (0x7fffc582, 1%nat, 0x1); (0x7fffc57a, 1%nat, 0x1); (0x7fffc575, 1%nat, 0x6); (0x7fffc56f, 1%nat, 0x2); (0x7fffc569, 1%nat, 0x5); (0x7fffc550, 1%nat, 0x3); (0x7fffc546, 1%nat, 0x2); (0x7fffc53e, 1%nat, 0x7); (0x7fffc536, 1%nat, 0x7); (0x7fffc52a, 1%nat, 0x6); (0x7fffc521, 1%nat, 0x7); (0x7fffc51d, 1%nat, 0x6); (0x7fffc519, 1%nat, 0x3); (0x7fffc512, 1%nat, 0x4); (0x7fffc50a, 1%nat, 0x2); (0x7fffc505, 1%nat, 0x4); (0x7fffc4fe, 1%nat, 0x5); (0x7fffc4f6, 1%nat, 0x2); (0x7fffc4f1, 1%nat, 0x4); (0x7fffc4ea, 1%nat, 0x2); (0x7fffc4e1, 1%nat, 0x1); (0x7fffc4dd, 1%nat, 0x1); (0x7fffc4d9, 1%nat, 0x4); (0x7fffc4d5, 1%nat, 0x3); (0x7fffc4d1, 1%nat, 0x1); (0x7fffc4cc, 1%nat, 0x6); (0x7fffc4c9, 1%nat, 0x1); (0x7fffc4c1, 1%nat, 0x2); (0x7fffc4bd, 1%nat, 0x5); (0x7fffc4b9, 1%nat, 0x3); (0x7fffc4b4, 1%nat, 0x2); (0x7fffc4b1, 1%nat, 0x1); (0x7fffc4ac, 1%nat, 0x1); (0x7fffc4a6, 1%nat, 0x6); (0x7fffc49a, 1%nat, 0x6); (0x7fffc491, 1%nat, 0x4); (0x7fffc488, 1%nat, 0x3); (0x7fffc481, 1%nat, 0x4); (0x7fffc478, 1%nat, 0x6); (0x7fffc475, 1%nat, 0x4); (0x7fffc46c, 1%nat, 0x3); (0x7fffc462, 1%nat, 0x3); (0x7fffc45b, 1%nat, 0x5); (0x7fffc44c, 1%nat, 0x4); (0x7fffc440, 1%nat, 0x6); (0x7fffc435, 1%nat, 0x4); (0x7fffc425, 1%nat, 0x5); (0x7fffc41f, 1%nat, 0x6); (0x7fffc419, 1%nat, 0x7); (0x7fffc415, 1%nat, 0x6); (0x7fffc410, 1%nat, 0x7); (0x7fffc40d, 1%nat, 0x1); (0x7fffc406, 1%nat, 0x4); (0x7fffc400, 1%nat, 0x6); (0x7fffc3fb, 1%nat, 0x6); (0x7fffc3f5, 1%nat, 0x4); (0x7fffc3f0, 1%nat, 0x7); (0x7fffc3ed, 1%nat, 0x2); (0x7fffc3e6, 1%nat, 0x6); (0x7fffc3e1, 1%nat, 0x7); (0x7fffc3dd, 1%nat, 0x2); (0x7fffc3d9, 1%nat, 0x1); (0x7fffc3d5, 1%nat, 0x1); (0x7fffc3d1, 1%nat, 0x3); (0x7fffc3ca, 1%nat, 0x1); (0x7fffc3c3, 1%nat, 0x1); (0x7fffc3bb, 1%nat, 0x1); (0x7fffc3b5, 1%nat, 0x2); (0x7fffc3b1, 1%nat, 0x1); (0x7fffc3a8, 1%nat, 0x3); (0x7fffc3a1, 1%nat, 0x5); (0x7fffc39a, 1%nat, 0x2); (0x7fffc395, 1%nat, 0x4); (0x7fffc391, 1%nat, 0x6); (0x7fffc387, 1%nat, 0x2); (0x7fffc37f, 1%nat, 0x6); (0x7fffc379, 1%nat, 0x5); (0x7fffc375, 1%nat, 0x5); (0x7fffc36f, 1%nat, 0x1); (0x7fffc366, 1%nat, 0x1); (0x7fffc361, 1%nat, 0x7); (0x7fffc35d, 1%nat, 0x7); (0x7fffc359, 1%nat, 0x7); (0x7fffc353, 1%nat, 0x6); (0x7fffc34d, 1%nat, 0x7); (0x7fffc349, 1%nat, 0x7); (0x7fffc345, 1%nat, 0x7); (0x7fffc33f, 1%nat, 0x2); (0x7fffc339, 1%nat, 0x7); (0x7fffc335, 1%nat, 0x4); (0x7fffc331, 1%nat, 0x6); (0x7fffc32d, 1%nat, 0x4); (0x7fffc329, 1%nat, 0x6); (0x7fffc323, 1%nat, 0x2); (0x7fffc31d, 1%nat, 0x5); (0x7fffc316, 1%nat, 0x5); (0x7fffc311, 1%nat, 0x2); (0x7fffc301, 1%nat, 0x3); (0x7fffc2fc, 1%nat, 0x2); (0x7fffc2f8, 1%nat, 0x4); (0x7fffc2f5, 1%nat, 0x4); (0x7fffc2de, 1%nat, 0x7)].
Definition ZERO_LIT : list (Z * Z) :=
  [(0xb6468, 5); (0x5d79a8, 38); (0x7fffa000, 8926); (0x7fffc2e4, 9); (0x7fffc2f4, 1); (0x7fffc300, 1); (0x7fffc304, 13); (0x7fffc314, 2); (0x7fffc31c, 1); (0x7fffc320, 3); (0x7fffc328, 1); (0x7fffc32c, 1); (0x7fffc330, 1); (0x7fffc334, 1); (0x7fffc338, 1); (0x7fffc33c, 3); (0x7fffc344, 1); (0x7fffc348, 1); (0x7fffc34c, 1); (0x7fffc350, 3); (0x7fffc358, 1); (0x7fffc35c, 1); (0x7fffc360, 1); (0x7fffc364, 2); (0x7fffc36c, 3); (0x7fffc374, 1); (0x7fffc378, 1); (0x7fffc37c, 3); (0x7fffc384, 3); (0x7fffc38c, 1); (0x7fffc390, 1); (0x7fffc394, 1); (0x7fffc398, 2); (0x7fffc3a0, 1); (0x7fffc3a4, 4); (0x7fffc3b0, 1); (0x7fffc3b4, 1); (0x7fffc3b8, 3); (0x7fffc3c0, 3); (0x7fffc3c8, 2); (0x7fffc3d0, 1); (0x7fffc3d4, 1); (0x7fffc3d8, 1); (0x7fffc3dc, 1); (0x7fffc3e0, 1); (0x7fffc3e4, 2); (0x7fffc3ec, 1); (0x7fffc3f4, 1); (0x7fffc3f8, 3); (0x7fffc404, 2); (0x7fffc40c, 1); (0x7fffc414, 1); (0x7fffc418, 1); (0x7fffc41c, 3); (0x7fffc424, 1); (0x7fffc428, 13); (0x7fffc43c, 4); (0x7fffc448, 4); (0x7fffc454, 7); (0x7fffc460, 2); (0x7fffc468, 4); (0x7fffc474, 1); (0x7fffc47c, 5); (0x7fffc48c, 5); (0x7fffc494, 6); (0x7fffc4a0, 6); (0x7fffc4b0, 1); (0x7fffc4b8, 1); (0x7fffc4bc, 1); (0x7fffc4c0, 1); (0x7fffc4c4, 5); (0x7fffc4d0, 1); (0x7fffc4d4, 1); (0x7fffc4d8, 1); (0x7fffc4dc, 1); (0x7fffc4e0, 1); (0x7fffc4e4, 1); (0x7fffc4e8, 2); (0x7fffc4f0, 1); (0x7fffc4f4, 2); (0x7fffc4fc, 2); (0x7fffc504, 1); (0x7fffc508, 2); (0x7fffc510, 2); (0x7fffc518, 1); (0x7fffc51c, 1); (0x7fffc520, 1); (0x7fffc524, 2); (0x7fffc528, 2); (0x7fffc530, 2); (0x7fffc534, 2); (0x7fffc53c, 2); (0x7fffc544, 2); (0x7fffc54c, 4); (0x7fffc558, 7); (0x7fffc564, 2); (0x7fffc568, 1); (0x7fffc56c, 3); (0x7fffc574, 1); (0x7fffc578, 2); (0x7fffc580, 2); (0x7fffc588, 5); (0x7fffc590, 3); (0x7fffc598, 1); (0x7fffc59c, 3); (0x7fffc5ac, 2); (0x7fffc5b4, 2); (0x7fffc5bc, 2); (0x7fffc5c0, 1); (0x7fffc5c4, 1); (0x7fffc5cc, 1); (0x7fffc5d0, 1); (0x7fffc5d4, 1); (0x7fffc5d8, 10); (0x7fffc5e8, 1); (0x7fffc5ec, 10); (0x7fffc5fc, 1); (0x7fffc600, 1); (0x7fffc604, 1); (0x7fffc60c, 1); (0x7fffc610, 1); (0x7fffc614, 5); (0x7fffc620, 1); (0x7fffc628, 1); (0x7fffc62c, 1); (0x7fffc630, 1); (0x7fffc634, 6); (0x7fffc640, 1); (0x7fffc644, 4); (0x7fffc650, 1); (0x7fffc654, 1); (0x7fffc658, 1); (0x7fffc65c, 6); (0x7fffc668, 4); (0x7fffc674, 1); (0x7fffc678, 3); (0x7fffc680, 2); (0x7fffc688, 4); (0x7fffc694, 1); (0x7fffc698, 4); (0x7fffc6a4, 2); (0x7fffc6ac, 2); (0x7fffc6b4, 2); (0x7fffc6b8, 1); (0x7fffc6bc, 3); (0x7fffc6c4, 1); (0x7fffc6c8, 1); (0x7fffc6cc, 4); (0x7fffc6d8, 5); (0x7fffc6e4, 4); (0x7fffc6f0, 3); (0x7fffc6f8, 1); (0x7fffc6fc, 2); (0x7fffc708, 2); (0x7fffc710, 1); (0x7fffc714, 1); (0x7fffc718, 3); (0x7fffc720, 1); (0x7fffc724, 3); (0x7fffc72c, 3); (0x7fffc734, 2); (0x7fffc73c, 1); (0x7fffc740, 2); (0x7fffc748, 3); (0x7fffc750, 2); (0x7fffc754, 4); (0x7fffc760, 2); (0x7fffc784, 1); (0x7fffc788, 2); (0x7fffc790, 1); (0x7fffc798, 1); (0x7fffc7a0, 1); (0x7fffc7a4, 1); (0x7fffc7a8, 4); (0x7fffc7b4, 1); (0x7fffc7b8, 4); (0x7fffc7c4, 4); (0x7fffc7d0, 5); (0x7fffc7dc, 1); (0x7fffc7e0, 4); (0x7fffc7ec, 1); (0x7fffc7f0, 1); (0x7fffc7f4, 5); (0x7fffc800, 6); (0x7fffc824, 6); (0x7fffc830, 6); (0x7fffc83c, 1); (0x7fffc840, 2); (0x7fffc848, 1); (0x7fffc84c, 4); (0x7fffc854, 4); (0x7fffc860, 3); (0x7fffc868, 1); (0x7fffc86c, 4); (0x7fffc878, 1); (0x7fffc87c, 5); (0x7fffc888, 2); (0x7fffc890, 1); (0x7fffc894, 1); (0x7fffc898, 2); (0x7fffc89c, 1); (0x7fffc8a0, 4); (0x7fffc8a8, 68); (0x7fffc8fc, 132); (0x7fffc9a0, 512); (0x7fffcc20, 16); (0x7fffcc34, 66957); (0x8000d1c4, 1); (0x8000d1c8, 1); (0x8000d1cc, 1); (0x8000d1d0, 1); (0x8000d1d4, 1); (0x8000d1d8, 1); (0x8000d1dc, 1); (0x8000d1e0, 1); (0x8000d1e4, 1); (0x8000d1e8, 1); (0x8000d1ec, 1); (0x8000d1f0, 1); (0x8000d1f4, 1); (0x8000d1f8, 1); (0x8000d1fc, 1); (0x8000d200, 2288); (0x8000daf4, 14); (0x8000db08, 8); (0x8000db14, 6); (0x8000db20, 100); (0x8000e39c, 682925); (0x800b4f4c, 1); (0x800b4f50, 5); (0x800b4f58, 17576)].
Definition FILL_LIT : list (Z * Z * Z) :=
  [(0x8000db84, 2072, 249); (0x800b4f55, 3, 249); (0x800b4f4d, 3, 249); (0x800b4f49, 3, 249); (0x8000db1a, 6, 249); (0x8000db10, 4, 249); (0x8000db02, 6, 249); (0x8000daf0, 4, 249); (0x8000d1fd, 3, 249); (0x8000d1f9, 3, 249); (0x8000d1f5, 3, 249); (0x8000d1f1, 3, 249); (0x8000d1ed, 3, 249); (0x8000d1e9, 3, 249); (0x8000d1e5, 3, 249); (0x8000d1e1, 3, 249); (0x8000d1dd, 3, 249); (0x8000d1d9, 3, 249); (0x8000d1d5, 3, 249); (0x8000d1d1, 3, 249); (0x8000d1cd, 3, 249); (0x8000d1c9, 3, 249); (0x8000d1c5, 3, 249); (0x8000d1c1, 3, 249); (0x7fffcc30, 4, 249); (0x7fffcba0, 128, 249); (0x7fffc980, 32, 249); (0x7fffc8ec, 16, 249); (0x7fffc8a4, 4, 249); (0x7fffc89e, 2, 249); (0x7fffc89a, 2, 249); (0x7fffc896, 2, 249); (0x7fffc892, 2, 249); (0x7fffc88b, 5, 249); (0x7fffc881, 7, 249); (0x7fffc87a, 2, 249); (0x7fffc871, 7, 249); (0x7fffc86a, 2, 249); (0x7fffc864, 4, 249); (0x7fffc859, 7, 249); (0x7fffc850, 4, 249); (0x7fffc84a, 2, 249); (0x7fffc843, 5, 249); (0x7fffc83e, 2, 249); (0x7fffc837, 5, 249); (0x7fffc82b, 5, 249); (0x7fffc821, 3, 249); (0x7fffc81d, 3, 249); (0x7fffc819, 3, 249); (0x7fffc815, 3, 249); (0x7fffc811, 3, 249); (0x7fffc80d, 3, 249); (0x7fffc807, 5, 249); (0x7fffc7fa, 6, 249); (0x7fffc7f2, 2, 249); (0x7fffc7ee, 2, 249); (0x7fffc7e5, 7, 249); (0x7fffc7dd, 3, 249); (0x7fffc7d6, 6, 249); (0x7fffc7c9, 7, 249); (0x7fffc7bd, 7, 249); (0x7fffc7b6, 2, 249); (0x7fffc7ad, 7, 249); (0x7fffc7a6, 2, 249); (0x7fffc7a2, 2, 249); (0x7fffc79d, 3, 249); (0x7fffc799, 3, 249); (0x7fffc795, 3, 249); (0x7fffc791, 3, 249); (0x7fffc78b, 5, 249); (0x7fffc786, 2, 249); (0x7fffc781, 3, 249); (0x7fffc77d, 3, 249); (0x7fffc779, 3, 249); (0x7fffc775, 3, 249); (0x7fffc771, 3, 249); (0x7fffc76d, 3, 249); (0x7fffc769, 3, 249); (0x7fffc763, 5, 249); (0x7fffc759, 7, 249); (0x7fffc752, 2, 249); (0x7fffc74c, 4, 249); (0x7fffc743, 5, 249); (0x7fffc73e, 2, 249); (0x7fffc739, 3, 249); (0x7fffc736, 2, 249); (0x7fffc730, 4, 249); (0x7fffc728, 4, 249); (0x7fffc722, 2, 249); (0x7fffc71c, 4, 249); (0x7fffc716, 2, 249); (0x7fffc712, 2, 249); (0x7fffc70b, 5, 249); (0x7fffc705, 3, 249); (0x7fffc6ff, 5, 249); (0x7fffc6fa, 2, 249); (0x7fffc6f4, 4, 249); (0x7fffc6e9, 7, 249); (0x7fffc6dd, 7, 249); (0x7fffc6d1, 7, 249); (0x7fffc6ca, 2, 249); (0x7fffc6c6, 2, 249); (0x7fffc6c0, 4, 249); (0x7fffc6ba, 2, 249); (0x7fffc6b6, 2, 249); (0x7fffc6af, 5, 249); (0x7fffc6a7, 5, 249); (0x7fffc69d, 7, 249); (0x7fffc696, 2, 249); (0x7fffc68d, 7, 249); (0x7fffc683, 5, 249); (0x7fffc67c, 4, 249); (0x7fffc676, 2, 249); (0x7fffc66d, 7, 249); (0x7fffc663, 5, 249); (0x7fffc65a, 2, 249); (0x7fffc656, 2, 249); (0x7fffc651, 3, 249); (0x7fffc649, 7, 249); (0x7fffc642, 2, 249); (0x7fffc63b, 5, 249); (0x7fffc632, 2, 249); (0x7fffc62e, 2, 249); (0x7fffc62a, 2, 249); (0x7fffc625, 3, 249); (0x7fffc621, 3, 249); (0x7fffc61a, 6, 249); (0x7fffc612, 2, 249); (0x7fffc60d, 3, 249); (0x7fffc609, 3, 249); (0x7fffc606, 2, 249); (0x7fffc602, 2, 249); (0x7fffc5fe, 2, 249); (0x7fffc5f7, 5, 249); (0x7fffc5ea, 2, 249); (0x7fffc5e3, 5, 249); (0x7fffc5d6, 2, 249); (0x7fffc5d2, 2, 249); (0x7fffc5ce, 2, 249); (0x7fffc5c9, 3, 249); (0x7fffc5c5, 3, 249); (0x7fffc5c1, 3, 249); (0x7fffc5be, 2, 249); (0x7fffc5b7, 5, 249); (0x7fffc5af, 5, 249); (0x7fffc5a9, 3, 249); (0x7fffc5a5, 3, 249); (0x7fffc5a0, 4, 249); (0x7fffc59a, 2, 249); (0x7fffc593, 5, 249); (0x7fffc58e, 2, 249); (0x7fffc583, 5, 249); (0x7fffc57b, 5, 249); (0x7fffc576, 2, 249); (0x7fffc570, 4, 249); (0x7fffc56a, 2, 249); (0x7fffc566, 2, 249); (0x7fffc55f, 5, 249); (0x7fffc551, 7, 249); (0x7fffc547, 5, 249); (0x7fffc53f, 5, 249); (0x7fffc537, 5, 249); (0x7fffc532, 2, 249); (0x7fffc52b, 5, 249); (0x7fffc526, 2, 249); (0x7fffc522, 2, 249); (0x7fffc51e, 2, 249); (0x7fffc51a, 2, 249); (0x7fffc513, 5, 249); (0x7fffc50b, 5, 249); (0x7fffc506, 2, 249); (0x7fffc4ff, 5, 249); (0x7fffc4f7, 5, 249); (0x7fffc4f2, 2, 249); (0x7fffc4eb, 5, 249); (0x7fffc4e5, 3, 249); (0x7fffc4e2, 2, 249); (0x7fffc4de, 2, 249); (0x7fffc4da, 2, 249); (0x7fffc4d6, 2, 249); (0x7fffc4d2, 2, 249); (0x7fffc4cd, 3, 249); (0x7fffc4ca, 2, 249); (0x7fffc4c2, 2, 249); (0x7fffc4be, 2, 249); (0x7fffc4ba, 2, 249); (0x7fffc4b5, 3, 249); (0x7fffc4b2, 2, 249); (0x7fffc4ad, 3, 249); (0x7fffc4a7, 5, 249); (0x7fffc49b, 5, 249); (0x7fffc492, 2, 249); (0x7fffc489, 3, 249); (0x7fffc482, 6, 249); (0x7fffc479, 3, 249); (0x7fffc476, 2, 249); (0x7fffc46d, 7, 249); (0x7fffc463, 5, 249); (0x7fffc45c, 4, 249); (0x7fffc44d, 7, 249); (0x7fffc441, 7, 249); (0x7fffc436, 6, 249); (0x7fffc426, 2, 249); (0x7fffc420, 4, 249); (0x7fffc41a, 2, 249); (0x7fffc416, 2, 249); (0x7fffc411, 3, 249); (0x7fffc40e, 2, 249); (0x7fffc407, 5, 249); (0x7fffc401, 3, 249); (0x7fffc3fc, 4, 249); (0x7fffc3f6, 2, 249); (0x7fffc3f1, 3, 249); (0x7fffc3ee, 2, 249); (0x7fffc3e7, 5, 249); (0x7fffc3e2, 2, 249); (0x7fffc3de, 2, 249); (0x7fffc3da, 2, 249); (0x7fffc3d6, 2, 249); (0x7fffc3d2, 2, 249); (0x7fffc3cb, 5, 249); (0x7fffc3c4, 4, 249); (0x7fffc3bc, 4, 249); (0x7fffc3b6, 2, 249); (0x7fffc3b2, 2, 249); (0x7fffc3a9, 7, 249); (0x7fffc3a2, 2, 249); (0x7fffc39b, 5, 249); (0x7fffc396, 2, 249); (0x7fffc392, 2, 249); (0x7fffc38d, 3, 249); (0x7fffc388, 4, 249); (0x7fffc380, 4, 249); (0x7fffc37a, 2, 249); (0x7fffc376, 2, 249); (0x7fffc370, 4, 249); (0x7fffc367, 5, 249); (0x7fffc362, 2, 249); (0x7fffc35e, 2, 249); (0x7fffc35a, 2, 249); (0x7fffc354, 4, 249); (0x7fffc34e, 2, 249); (0x7fffc34a, 2, 249); (0x7fffc346, 2, 249); (0x7fffc340, 4, 249); (0x7fffc33a, 2, 249); (0x7fffc336, 2, 249); (0x7fffc332, 2, 249); (0x7fffc32e, 2, 249); (0x7fffc32a, 2, 249); (0x7fffc324, 4, 249); (0x7fffc31e, 2, 249); (0x7fffc317, 5, 249); (0x7fffc312, 2, 249); (0x7fffc302, 2, 249); (0x7fffc2fd, 3, 249); (0x7fffc2f9, 3, 249); (0x7fffc2f6, 2, 249); (0x7fffc2ed, 7, 249); (0x7fffc2df, 5, 249)].
Definition WR_LIT : list (Z * Z) :=
  [(0x7fffa000, 0xbf400); (0xa8000, 0x562000)].

(* [comment removed for export] *)
Definition kimg_covb (k : list kentry) (lo hi : Z) : bool :=
  existsb (fun K => match K with KImg lo' hi' => (lo' <=? lo) && (hi <=? hi') | _ => false end)%bool k.
Definition chk_img_none (cs : acs) : bool :=
  forallb (fun p => kimg_covb (kn cs) (fst p) (snd p) && (img_lo ASAN <=? fst p) && (snd p <=? img_hi ASAN))%bool IMG_NONE.
Definition chk_words (cs : acs) (img : bool) (l : list (Z * nat * Z)) : bool :=
  forallb (fun t => match t with (a, w, v) =>
     existsb (kentry_eqb (KWord (SA (ELit 0) a) w (ELit v))) (kn cs)
     && (if img then (img_lo ASAN <=? a) && (a + Z.of_nat w <=? img_hi ASAN) else (img_hi ASAN <=? a) && (a + Z.of_nat w <=? CEIL)) end)%bool l.
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
  (expr_eqb (sr_get (s_regs (a_ss cs)) 1) (ELit 0x982ac)
   && expr_eqb (sr_get (s_regs (a_ss cs)) 2) (EAlu Instr.ALU_ADD e_sp0' (ELit (-48)))
   && expr_eqb (sr_get (s_regs (a_ss cs)) 3) (ELit 0x10800)
   && expr_eqb (sr_get (s_regs (a_ss cs)) 4) (ELit 0x5e83d8)
   && expr_eqb (sr_get (s_regs (a_ss cs)) 10) (EVar 1)
   && expr_eqb (sr_get (s_regs (a_ss cs)) 11) (EAlu Instr.ALU_ADD e_sp0' (ELit 8)))%bool.
Definition chk_stack (cs : acs) : bool :=
  (existsb (kentry_eqb (KWr (SA e_sp0' (-8388608)) (ELit 8388608))) (kn cs)
   && existsb (kentry_eqb (KWord (SA e_sp0' 8) 8 e_p0a)) (kn cs)
   && existsb (kentry_eqb (KWord (SA e_sp0' 16) 8 e_p1)) (kn cs)
   && existsb (kentry_eqb (KWord (SA (ELit 0) 0x5e8330) 4 (EVar 44))) (kn cs)
   && existsb (kentry_eqb (KRange (EVar 44) 1 4194303)) (kn cs))%bool.
Definition chk_all (cs : acs) : bool :=
  (chk_img_none cs && chk_words cs true IMG_WORDS && chk_words cs false EXT_WORDS && chk_zero cs && chk_fill cs && chk_wr cs
   && chk_regs cs && chk_stack cs && afd_eqb (a_fd cs) FdStd)%bool.

(* [comment removed for export] *)
Definition chk_words_m (M : kentry -> bool) (cs : acs) (img : bool) (l : list (Z * nat * Z)) : bool :=
  forallb (fun t => match t with (a, w, v) =>
     M (KWord (SA (ELit 0) a) w (ELit v))
     && (if img then (img_lo ASAN <=? a) && (a + Z.of_nat w <=? img_hi ASAN) else (img_hi ASAN <=? a) && (a + Z.of_nat w <=? CEIL)) end)%bool l.
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
   && M (KWord (SA (ELit 0) 0x5e8330) 4 (EVar 44))
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
Lemma chk_all_1 : chk_all HS_asan2_1 = true. Proof. apply chk_all_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_all_2 : chk_all HS_asan2_2 = true. Proof. apply chk_all_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_all_3 : chk_all HS_asan2b_1 = true. Proof. apply chk_all_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_all_4 : chk_all HS_asan2b_2 = true. Proof. apply chk_all_fast. vm_cast_no_check (@eq_refl bool true). Qed.

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
  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
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
    mp_ra  : getr R 1 = Z_to_bv 64 0x982ac;
    mp_sp  : getr R 2 = Z_to_bv 64 (usp - 48);
    mp_gp  : getr R 3 = Z_to_bv 64 0x10800;
    mp_tp  : getr R 4 = Z_to_bv 64 0x5e83d8;
    mp_a0  : getr R 10 = Z_to_bv 64 argc;
    mp_a1  : getr R 11 = Z_to_bv 64 (usp + 8);
    mp_halt : m_halted md = None;
    mp_fs   : m_fs md = fs;
    mp_fds  : m_fds md = fds_std;
    mp_limit : vm_limit (m_vmmaps md) = LIM;
    (* [comment removed for export] *)
    mp_tid  : exists tid, 1 <= tid <= 4194303 /\ rdn ASEGS FULL (Z_to_bv 64 0x5e8330) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
    (* [comment removed for export] *)
    mp_argblock : forall a, argH (E0 APH sp rdraw brk0 argv envp uid hw) a = true -> FULL a = wrap_mem APH sp argv envp uid hw rdraw a;
    (* [comment removed for export] *)
    mp_argv0p : forall j, (j < 8)%nat -> FULL (Z_to_bv 64 (usp + 8 + Z.of_nat j)) = Some (nth j (word_to_le_bytes 8 (Z_to_bv 64 p0a)) (Z_to_bv 8 0));
    mp_argv1p : 2 <= argc -> forall j, (j < 8)%nat -> FULL (Z_to_bv 64 (usp + 16 + Z.of_nat j)) = Some (nth j (word_to_le_bytes 8 (Z_to_bv 64 p1a)) (Z_to_bv 8 0));
    (* [comment removed for export] *)
    mp_stack : forall i, 0 <= i < 8388608 -> FULL (Z_to_bv 64 (usp - 8388608 + i)) <> None;
    (* [comment removed for export] *)
    mp_img_none : forall lo hi a, In (lo, hi) IMG_NONE -> lo <= a < hi -> FULL (Z_to_bv 64 a) = None;
    mp_img_words : forall a w v, In (a, w, v) IMG_WORDS -> rdn ASEGS FULL (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v));
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
    Hypothesis CS : cs_ok ASEGS ASAN LIM SINV argH fs E cs R FULL model.

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
                        ltac:(cbn [edenot]; rewrite u_lit64a; reflexivity) 0x5e8330 4 (EVar 44) H5
                        ltac:(cbn [img_lo ASAN]; lia) ltac:(cbn [img_hi ASAN]; lia)) as X.
          cbn [edenot] in X. rewrite Z_to_bv_bv_unsigned. exact X.
      - (* [comment removed for export] *) exact (pre_argblock sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS).
      - (* [comment removed for export] *)
        intros j Hj.
        pose proof (pre_word_at sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS e_sp0' usp U_sp0 8 8 e_p0a H7 ltac:(lia) ltac:(lia)) as X.
        assert (Hrom : forall k, (k < 8)%nat -> seg_rom ASEGS (Z_to_bv 64 (usp + 8 + Z.of_nat k)) = None).
        { intros k Hk. apply (seg_rom_off_hull ASEGS ASAN asan_in_hull). unfold in_hull. rewrite u_lit64a, Z.mod_small by lia.
          cbn [img_lo img_hi ASAN]. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
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
        assert (Hrom : forall k, (k < 8)%nat -> seg_rom ASEGS (Z_to_bv 64 (usp + 16 + Z.of_nat k)) = None).
        { intros k Hk. apply (seg_rom_off_hull ASEGS ASAN asan_in_hull). unfold in_hull. rewrite u_lit64a, Z.mod_small by lia.
          cbn [img_lo img_hi ASAN]. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
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
        intros k Hk. apply (find_segment1_none_outside ASEGS (img_lo ASAN) (img_hi ASAN) _ asan_segs_in_hull). cbn [img_lo img_hi ASAN]. right. lia.
      - (* [comment removed for export] *)
        intros lo hi a Hin Ha. unfold chk_img_none in Cimg. apply forallb_forall with (x := (lo, hi)) in Cimg; [|exact Hin].
        cbn [fst snd] in Cimg. apply andb_prop in Cimg as [Cimg C3]. apply andb_prop in Cimg as [C1 C2].
        apply Z.leb_le in C2. apply Z.leb_le in C3. cbn [img_lo img_hi ASAN] in C2, C3.
        unfold kimg_covb in C1. apply existsb_exists in C1 as [K [HK HK2]]. destruct K; try discriminate.
        apply andb_prop in HK2 as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
        pose proof (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ CS) _ HK) as KO. cbn [kentry_ok] in KO. (first [ dand3 KO as _ _ KO | destruct KO as (_ & _ & KO) ]).
        rewrite <- (Mr_image sp rdraw argv envp uid hw Hsp Hva cs E FULL model); [apply KO; lia|].
        rewrite u_lit64a, Z.mod_small by lia. cbn [img_lo img_hi ASAN]. lia.
      - (* [comment removed for export] *)
        intros a w v Hin. unfold chk_words in Cw. apply forallb_forall with (x := (a, w, v)) in Cw; [|exact Hin].
        apply andb_prop in Cw as [C1 C2]. apply andb_prop in C2 as [C2 C3]. apply Z.leb_le in C2. apply Z.leb_le in C3.
        pose proof (pre_word_img_at sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS (ELit 0) 0
                      ltac:(cbn [edenot]; rewrite u_lit64a; reflexivity) a w (ELit v) C1 ltac:(lia) ltac:(lia)) as X.
        cbn [edenot] in X. exact X.
      - (* [comment removed for export] *)
        intros a w v Hin j Hj. unfold chk_words in Cx. apply forallb_forall with (x := (a, w, v)) in Cx; [|exact Hin].
        apply andb_prop in Cx as [C1 C2]. apply andb_prop in C2 as [C2 C3]. apply Z.leb_le in C2. apply Z.leb_le in C3.
        cbn [img_hi ASAN] in C2. unfold CEIL in C3.
        pose proof (pre_word_at sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS (ELit 0) 0
                      ltac:(cbn [edenot]; rewrite u_lit64a; reflexivity) a w (ELit v) C1 ltac:(lia) ltac:(lia)) as X.
        cbn [edenot] in X. rewrite Z.add_0_l in X. apply X; [|exact Hj].
        intros k Hk. apply (seg_rom_off_hull ASEGS ASAN asan_in_hull). unfold in_hull. rewrite u_lit64a, Z.mod_small by lia.
        cbn [img_lo img_hi ASAN]. apply andb_false_iff. right. apply Z.ltb_ge. lia.
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
