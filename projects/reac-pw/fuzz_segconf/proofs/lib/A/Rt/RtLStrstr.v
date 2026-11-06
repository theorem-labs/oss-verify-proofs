(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names, addresses and numbers changed; 520 of its 641 lines of code are new or changed and 714 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/reply.v, with its module paths and module names changed; 399 of its 440 lines of code are new or changed and 600 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMstrstr.v, with its module paths and module names changed; 266 of its 409 lines of code are new or changed and 297 lines of the source are left out. *)
(* Row 8 of the interceptor interface (provenance/evidence/interceptors/INTERFACE-A-interceptors.md): strstr at
   SegRtPC.PC_strstr = 0x43a24 (trampoline -> __interceptor_strstr 0x455b8 -> musl strstr 0x9b000, which calls the
   strchr interceptor and, for a needle of 5 bytes or more, twoway_strstr with the memcmp and memchr interceptors ->
   StrstrCheck), stated as RtSeg.astrstr_realizes at the stack-protector pair RtAPI.A_SSP_GOT / A_SSP_GUARD
   (0xa36d8 -> 0x5ff078, read by twoway_strstr).
   - the walk: A/FMss_strstr_wrap.v strstr_wrap_holds (relocated from omx-clap-core/fuzz_manifest), a lib/Lib walk
     from the trampoline to the return over the local-shadow statements A/FMss_*.v;
   - it is RUN on the cleaned store (RtBzClean.clean: our contracts give no `mem_inv`), as a lib/A/Bz walk
     (RtBzClean.lib_evt_bz: one step body, one image) through RtBzClean.bz_run_clean, and its post read back by
     RtBzAdaptP.art_post_ro_clean (the walk writes only its 4608-byte stack window);
   - the premises: our astr_at / aread_ok / atail_vis / aguard_ok / rt_rom_view give the walk's byte, range-check,
     shadow, separation and guard premises; the runtime's fixed cells (AsanRT.asan_cells, the real-function cells,
     common_flags' bytes) come from the record's constant table (AF0x.tfib_const_lookup);
   - the answer: the walk returns Spec/StrStr.v strstr_val, which strstr_val_spec reads as RtSeg's first_occ /
     no_occ (the list facts of fuzz_manifest's lib/A/FMspec_str.v).
   The pattern is fuzz_manifest's lib/A/FMstrstr.v fm_astrstr, restated on RtSeg's premises. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import
RtDefs RtBzHBase RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg SegRtPC RtAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Img0 AsanRT.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require FMss_shv FMss_TwAsan FMss_strstr_wrap_c FMss_strstr_wrap.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require strstr_wrap_c asan_memcpy memchr_c memcmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Spec Require StrStr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require I_qck Shadow.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module LM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.
Module LF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Frame.
Module LS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.MState.
Module LP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.PropExec.
Module LX := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Exec.
Module IM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Img0.
Module ART := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.AsanRT.
Module SHV := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.FMss_shv.
Module TWA := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.FMss_TwAsan.
Module SSWc := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.FMss_strstr_wrap_c.
Module SSW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.FMss_strstr_wrap.
Module SWc := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.strstr_wrap_c.
Module AMC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.asan_memcpy.
Module MCc := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memchr_c.
Module MPc := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memcmp_c.
Module SST := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Spec.StrStr.
Module BzQ := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_qck.
Module BzS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.Shadow.

(* ---- the walk's answer, in RtSeg's words (fm lib/A/FMspec_str.v:14-85) ---- *)

Lemma prefix_eqb_spec : forall (w t : list Z),
  SST.prefix_eqb w t = true <-> ((length w <= length t)%nat /\ firstn (length w) t = w).
Proof.
  induction w as [|a w IH]; intros t; cbn [SST.prefix_eqb length firstn].
  - split; [intros _; split; [lia | reflexivity] | reflexivity].
  - destruct t as [|b t]; cbn [length firstn].
    + split; [discriminate | intros (H & _); lia].
    + rewrite andb_true_iff, Z.eqb_eq, (IH t). split.
      * intros (-> & Hlen & Hfst). split; [lia|]. rewrite Hfst. reflexivity.
      * intros (Hlen & Heq). injection Heq as -> Hfst. split; [reflexivity | split; [lia | exact Hfst]].
Qed.

Lemma prefix_eqb_occ : forall (t w : list Z), SST.prefix_eqb w t = true <-> RtSeg.occ_at t w 0.
Proof.
  intros t w. rewrite prefix_eqb_spec. unfold RtSeg.occ_at. cbn [skipn].
  split; intros (H1 & H2); (split; [lia | exact H2]).
Qed.

Lemma occ_at_cons : forall (b : Z) (t w : list Z) (j : nat),
  RtSeg.occ_at (b :: t) w (S j) <-> RtSeg.occ_at t w j.
Proof.
  intros b t w j. unfold RtSeg.occ_at. cbn [length skipn]. split; intros (H1 & H2); (split; [lia | exact H2]).
Qed.

Lemma find_first_some : forall (t w : list Z) (j : nat),
  SST.find_first t w = Some j -> RtSeg.first_occ t w j.
Proof.
  induction t as [|b t IH]; intros w j Hf.
  - cbn in Hf. destruct (SST.prefix_eqb w []) eqn:EP; [|discriminate].
    injection Hf as <-. split; [apply prefix_eqb_occ; exact EP | intros j' Hj'; lia].
  - cbn [SST.find_first] in Hf. destruct (SST.prefix_eqb w (b :: t)) eqn:EP.
    + injection Hf as <-. split; [apply prefix_eqb_occ; exact EP | intros j' Hj'; lia].
    + destruct (SST.find_first t w) as [k|] eqn:EF; [|discriminate].
      cbn [option_map] in Hf. injection Hf as <-.
      destruct (IH w k EF) as (Hocc & Hmin).
      split; [apply occ_at_cons; exact Hocc|].
      intros j' Hj'. destruct j' as [|j''].
      * intros Hc. rewrite (proj2 (prefix_eqb_occ (b :: t) w) Hc) in EP. discriminate.
      * intros Hc. apply (Hmin j'' ltac:(lia)). apply (proj1 (occ_at_cons b t w j'')). exact Hc.
Qed.

Lemma find_first_none : forall (t w : list Z),
  SST.find_first t w = None -> RtSeg.no_occ t w.
Proof.
  induction t as [|b t IH]; intros w Hf j.
  - cbn in Hf. destruct (SST.prefix_eqb w []) eqn:EP; [discriminate|].
    intros Hc. destruct j as [|j'].
    + rewrite (proj2 (prefix_eqb_occ [] w) Hc) in EP. discriminate.
    + unfold RtSeg.occ_at in Hc. cbn [length skipn] in Hc. lia.
  - cbn [SST.find_first] in Hf. destruct (SST.prefix_eqb w (b :: t)) eqn:EP; [discriminate|].
    destruct (SST.find_first t w) as [k|] eqn:EF; [cbn [option_map] in Hf; discriminate|].
    intros Hc. destruct j as [|j'].
    + rewrite (proj2 (prefix_eqb_occ (b :: t) w) Hc) in EP. discriminate.
    + apply (IH w EF j'). apply (proj1 (occ_at_cons b t w j')). exact Hc.
Qed.

Theorem strstr_val_spec : forall (A : Z) (hb nb : list byte),
  (SST.strstr_val A hb nb = 0 /\
   RtSeg.no_occ (map (fun b : byte => bv_unsigned b) hb) (map (fun b : byte => bv_unsigned b) nb))
  \/ (exists j, RtSeg.first_occ (map (fun b : byte => bv_unsigned b) hb) (map (fun b : byte => bv_unsigned b) nb) j
                /\ SST.strstr_val A hb nb = A + Z.of_nat j).
Proof.
  intros A hb nb. unfold SST.strstr_val.
  destruct (SST.find_first (map bv_unsigned hb) (map bv_unsigned nb)) as [j|] eqn:EF.
  - right. exists j. split; [apply find_first_some; exact EF | reflexivity].
  - left. split; [reflexivity | apply find_first_none; exact EF].
Qed.

(* ---- bytes: the donor's reader and lib/Lib's (fm lib/A/FMstrstr.v:67-241) ---- *)

Lemma view_mrd : forall (H : word -> bool) mem a v,
  aview tfibsegs H mem a = Some v ->
  exists b, LM.mrd IM.rsegs (mrestrict H mem) (LM.wa a) = Some b /\ bv_unsigned b = v.
Proof.
  intros H mem a v E. unfold aview in E.
  destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:Eb; [|discriminate].
  cbn in E. injection E as <-. exists b. split; [exact Eb | reflexivity].
Qed.

Lemma view_some_mrd : forall (H : word -> bool) mem a, aview tfibsegs H mem a <> None ->
  exists b, LM.mrd IM.rsegs (mrestrict H mem) (LM.wa a) = Some b.
Proof.
  intros H mem a E. destruct (aview tfibsegs H mem a) as [v|] eqn:Ev; [|exfalso; exact (E eq_refl)].
  destruct (view_mrd H mem a v Ev) as (b & Eb & _). exists b. exact Eb.
Qed.

(* the interceptor's range check (AsanRT addressable) from the contract's range_addressable *)
Lemma addressable_of_view : forall (H : word -> bool) mem p n,
  0 <= p -> 0 <= n -> p + n <= ART.APPMEM_END -> (forall i, 0 <= i < n -> ART.app_mem (p + i)) ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF p n ->
  ART.addressable (mrestrict H mem) p n.
Proof.
  intros H mem p n Hp Hn Hpn Happ HRA. split; [exact Hp|]. split; [exact Hn|]. split; [exact Hpn|].
  intros i Hi. split; [exact (Happ i Hi)|].
  destruct (HRA (p + i) ltac:(lia)) as (s & Hs & Hok).
  destruct (view_mrd H mem _ _ Hs) as (b & Eb & Ub).
  exists b. split.
  - replace (ART.shadow_addr (p + i)) with (shadow_of_addr SHADOW_OFF (p + i))
      by (unfold ART.shadow_addr, shadow_of_addr, SHADOW_OFF, ART.ASAN_K; lia). exact Eb.
  - pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
    assert (Sb : bv_unsigned b < 128 -> bv_signed b = bv_unsigned b).
    { intros Hl. unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128. lia. }
    unfold ART.shadow_ok. unfold saddr_ok in Hok. rewrite <- Ub in Hok.
    destruct Hok as [H0|[H1 H2]]; [left | right]; rewrite Sb by lia; lia.
Qed.

(* the walks' local shadow premise from the contract's shadow hull *)
Lemma shvis_of_hull : forall (H : word -> bool) mem p n,
  shadow_hull_vis (aview tfibsegs H mem) p n -> SHV.shvis (mrestrict H mem) p n.
Proof.
  intros H mem p n HV Hn s Hs. apply view_some_mrd. apply HV.
  assert (E1 : forall q, BzQ.al8 (BzS.shad q) = shadow_addr q / 8 * 8).
  { intros q. unfold BzQ.al8, BzS.shad, BzS.SHB, shadow_addr, SHADOW_OFF. rewrite (Z.add_comm (q / 8)). lia. }
  rewrite !E1 in Hs. exact Hs.
Qed.

(* an application byte range (amem_range) is lib/Lib app_mem byte by byte *)
Lemma app_of_amem : forall p n, 0 <= p -> amem_range p n -> forall i, 0 <= i < n -> ART.app_mem (p + i).
Proof.
  intros p n Hp HA i Hi. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HA.
  unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. lia.
Qed.

(* lib/Lib's mrd, bytes_at and stk are lib/A/Bz's over the same image, so the Bz transfer lemmas read them *)
Lemma mrd_cleanL : forall m (a : word), rom_eq m -> bv_unsigned a < 2 ^ 47 ->
  LM.mrd IM.rsegs (clean m) a = LM.mrd IM.rsegs m a.
Proof. intros m a HE Ha. exact (mrd_clean m a HE ltac:(unfold BM.UTOP; lia)). Qed.

Lemma bytes_at_cleanL : forall m a bs, rom_eq m -> a + Z.of_nat (length bs) <= 2 ^ 47 ->
  LM.bytes_at IM.rsegs m a bs -> LM.bytes_at IM.rsegs (clean m) a bs.
Proof. intros m a bs HE Hu H. exact (bytes_at_clean m a bs HE ltac:(unfold BM.UTOP; lia) H). Qed.

Lemma stk_cleanL : forall m lo hi, TFIB_IMG_END <= lo -> hi <= 2 ^ 47 ->
  LF.stk IM.rsegs m lo hi -> LF.stk IM.rsegs (clean m) lo hi.
Proof. intros m lo hi Hlo Hhi H. exact (stk_clean m lo hi Hlo ltac:(unfold BM.UTOP; lia) H). Qed.

Lemma wa_lt47 : forall a, 0 <= a < 2 ^ 47 -> bv_unsigned (LM.wa a) < 2 ^ 47.
Proof. intros a Ha. rewrite LM.wa_unsigned by lia. lia. Qed.

Lemma addressable_cleanL : forall m p n, rom_eq m -> ART.addressable m p n -> ART.addressable (clean m) p n.
Proof.
  intros m p n HE (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|].
  exists b. split; [| exact Hok]. rewrite mrd_cleanL; [exact Hb | exact HE |].
  apply wa_lt47. unfold ART.shadow_addr, ART.ASAN_K. unfold ART.APPMEM_END in H2.
  assert (0 <= (p + i) / 8 <= p + i) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia.
Qed.

Lemma shvis_cleanL : forall m p n, rom_eq m -> 0 <= p -> p + n <= 2 ^ 47 -> SHV.shvis m p n ->
  SHV.shvis (clean m) p n.
Proof.
  intros m p n HE Hp Hpn H Hn s Hs. destruct (H Hn s Hs) as (b & Hb). exists b.
  rewrite mrd_cleanL; [exact Hb | exact HE |]. apply wa_lt47.
  unfold BzQ.al8, BzS.shad, BzS.SHB in Hs.
  assert (0 <= p / 8 <= p) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (0 <= (p + n - 1) / 8 <= p + n - 1) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  Z.div_mod_to_equations. lia.
Qed.

Lemma le8_wa : forall v, 0 <= v < 2 ^ 64 -> LM.le8 (LM.wa v) = Z_to_le_bytes 8 v.
Proof. intros v Hv. unfold LM.le8, word_to_le_bytes, LM.wa. rewrite LS.unsigned_lit by exact Hv. reflexivity. Qed.

Lemma le4_wa : forall v, 0 <= v < 2 ^ 32 -> LM.le4 (LM.wa v) = Z_to_le_bytes 4 v.
Proof. intros v Hv. unfold LM.le4, LM.wa. rewrite LS.unsigned_lit by lia. reflexivity. Qed.

(* the contracts' band room keeps a range below 2^47 *)
Lemma amem_top : forall p n, amem_range p n -> p + n <= 2 ^ 47.
Proof. intros p n H. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in H. lia. Qed.

(* a range that ends below a 16-aligned sp minus 8192 ends, rounded up to its 8-byte word, below sp - 4608 *)
Lemma round_sep : forall e sp, sp mod 16 = 0 -> e + 1 <= sp - 8192 -> e + 1 + (7 - e mod 8) <= sp - 4608.
Proof. intros e sp H1 H2. Z.div_mod_to_equations. lia. Qed.

(* ---- the runtime cells the walk reads, from the record's constant table ---- *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : SegBSyms B.

Lemma cell_lib : forall ly S H mem a (w : nat) v, ARm B ly S (aview tfibsegs H mem) ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
  0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_nat w) ->
  LM.bytes_at IM.rsegs (mrestrict H mem) a (Z_to_le_bytes w v).
Proof.
  intros ly S H mem a w v M E Ha Hw Hv.
  pose proof (tfib_const_lookup B TB ly S H mem a w v M E) as VM.
  split; [exact Ha|]. rewrite LM.length_Z_to_le_bytes. split; [exact Hw|].
  intros i Hi. rewrite (RtBzPre.nth_le_bytes w v i Hi).
  change (LM.mrd IM.rsegs (mrestrict H mem) (LM.wa (a + Z.of_nat i)))
    with (mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat i)).
  rewrite (VM i Hi). f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
  rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat w))) by exact Hv.
  change (bv_modulus 8) with 256. rewrite ?Z.mod_mod by lia. reflexivity.
Qed.

Lemma cell8 : forall ly S H mem a v, rom_eq (mrestrict H mem) -> ARm B ly S (aview tfibsegs H mem) ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 8 (AV (ANum v))) ->
  0 <= a -> a + 8 <= 2 ^ 47 -> 0 <= v < 2 ^ 64 ->
  LM.bytes_at IM.rsegs (clean (mrestrict H mem)) a (LM.le8 (LM.wa v)).
Proof.
  intros ly S H mem a v RE M E Ha Ha8 Hv. rewrite le8_wa by exact Hv.
  apply bytes_at_cleanL; [exact RE | rewrite LM.length_Z_to_le_bytes; lia |].
  exact (cell_lib ly S H mem a 8 v M E Ha ltac:(lia) Hv).
Qed.

Lemma cell4 : forall ly S H mem a v, rom_eq (mrestrict H mem) -> ARm B ly S (aview tfibsegs H mem) ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 4 (AV (ANum v))) ->
  0 <= a -> a + 4 <= 2 ^ 47 -> 0 <= v < 2 ^ 32 ->
  LM.bytes_at IM.rsegs (clean (mrestrict H mem)) a (LM.le4 (LM.wa v)).
Proof.
  intros ly S H mem a v RE M E Ha Ha4 Hv. rewrite le4_wa by exact Hv.
  apply bytes_at_cleanL; [exact RE | rewrite LM.length_Z_to_le_bytes; lia |].
  exact (cell_lib ly S H mem a 4 v M E Ha ltac:(lia) Hv).
Qed.

Lemma cell1 : forall ly S H mem a v, rom_eq (mrestrict H mem) -> ARm B ly S (aview tfibsegs H mem) ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 1 (AV (ANum v))) ->
  0 <= a -> a + 1 <= 2 ^ 47 -> 0 <= v < 256 ->
  LM.bytes_at IM.rsegs (clean (mrestrict H mem)) a [Z_to_bv 8 v].
Proof.
  intros ly S H mem a v RE M E Ha Ha1 Hv.
  apply bytes_at_cleanL; [exact RE | cbn [length]; lia |].
  exact (cell_lib ly S H mem a 1 v M E Ha ltac:(lia) Hv).
Qed.

Local Ltac cellk RE M :=
  first
    [ apply (cell8 _ _ _ _ _ _ RE M); [vm_compute; reflexivity | lia | lia | lia]
    | apply (cell4 _ _ _ _ _ _ RE M); [vm_compute; reflexivity | lia | lia | lia]
    | apply (cell1 _ _ _ _ _ _ RE M); [vm_compute; reflexivity | lia | lia | lia] ].

Lemma asan_cells_of_ARm : forall ly S H mem, rom_eq (mrestrict H mem) -> ARm B ly S (aview tfibsegs H mem) ->
  ART.asan_cells (clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M. unfold ART.asan_cells, ART.CELL_K, ART.ASAN_K, ART.GOT_CELL_K, ART.INITED, ART.REPLACE,
    ART.GOT_REPLACE, ART.UAR, ART.GOT_UAR, ART.CANPOISON, ART.HIEND, ART.GOT_HIEND, ART.MIDBEG, ART.GOT_MIDBEG,
    ART.MIDEND, ART.GOT_MIDEND, ART.REAL_MEMCPY, ART.REAL_MEMSET, ART.GOT_REAL_MEMSET, ART.MUSL_MEMCPY,
    ART.MUSL_MEMSET.
  repeat match goal with |- _ /\ _ => split end.
  all: cellk RE M.
Qed.

End k.

(* the same, outside the Section: the record B and TB are arguments; the walk's cell addresses and values are
   Definitions of strstr_wrap_c / memchr_c / memcmp_c, unfolded first so that lia reads them *)
Ltac unf_cells :=
  repeat (first [ progress unfold SWc.REAL_STRSTR | progress unfold SWc.STRSTR | progress unfold SWc.REAL_STRCHR
                 | progress unfold SWc.STRCHR | progress unfold SWc.REAL_MEMCHR | progress unfold SWc.REAL_MEMCMP
                 | progress unfold SWc.GOT_CF | progress unfold SWc.CF | progress unfold MCc.MEMCHR
                 | progress unfold MPc.MEMCMP ]).
Ltac cellc B TB RE M :=
  unf_cells;
  first
    [ apply (cell8 B TB _ _ _ _ _ _ RE M); [vm_compute; reflexivity | lia | lia | lia]
    | apply (cell4 B TB _ _ _ _ _ _ RE M); [vm_compute; reflexivity | lia | lia | lia]
    | apply (cell1 B TB _ _ _ _ _ _ RE M); [vm_compute; reflexivity | lia | lia | lia] ].

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : SegBSyms B.

Theorem seg_strstr : RtSeg.astrstr_realizes tfibsegs B SegRtPC.PC_strstr RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof.
  unfold RtSeg.astrstr_realizes.
  intros ly S W regs mem md x y st sw HG HPRE G10 G11 Hx0 Hy0 SX SY RDX AMX RDY AMY TX TY HROM.
  pose proof HPRE as (HEP & _ & _).
  pose proof HEP as (HAR & _ & HAL & _).
  pose proof (amem_top x _ AMX) as AMX'.
  pose proof (amem_top y _ AMY) as AMY'.
  pose proof RDX as (_ & _ & HNX & _ & _ & XRA & XHV).
  pose proof RDY as (_ & _ & HNY & _ & _ & YRA & YHV).
  assert (EX : astr_len st = Z.of_nat (length st)) by reflexivity.
  assert (EY : astr_len sw = Z.of_nat (length sw)) by reflexivity.
  assert (SPE : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
  set (m := mrestrict (w_H W) mem) in *.
  (* 1. the read-only views and the cleaned store *)
  pose proof (RtBzAdapt.rom_eq_of_rt B TB ly S W mem md HAR HROM) as ROMEQ.
  set (mc := clean m).
  (* 2. the stack window *)
  destruct (RtBzAdapt.stk_of_stk_pre B (2 * ESTACK) ly S W regs mem md HPRE ltac:(unfold ESTACK; lia))
    as (ST0 & HC0 & HCs & Hsp47).
  (* 3. the two strings: the haystack with its NUL and the rest of the NUL's word, the needle with its NUL *)
  destruct (RtBzAdapt.bz_str_slack W mem x st SX TX ltac:(lia) ltac:(lia)) as (BXm & SLK).
  set (hs := RtBzAdapt.tail_bytes W mem (x + astr_len st)) in *.
  pose proof (RtBzAdapt.tail_bytes_length W mem (x + astr_len st)) as LHS. fold hs in LHS.
  pose proof (RtBzAdapt.bz_str_bytes W mem y sw SY ltac:(lia) ltac:(lia)) as BYm.
  assert (HX : bv_unsigned (getr regs 10) = x) by (rewrite G10; unfold w64; apply LS.unsigned_lit; lia).
  assert (HY : bv_unsigned (getr regs 11) = y) by (rewrite G11; unfold w64; apply LS.unsigned_lit; lia).
  (* 4. the stack-protector pair musl's twoway_strstr reads *)
  destruct (RtBzAdapt.bz_guard_bytes W mem RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD HG
              ltac:(unfold RtAPI.A_SSP_GOT; lia) ltac:(unfold RtAPI.A_SSP_GOT; lia)
              ltac:(unfold RtAPI.A_SSP_GUARD; lia) ltac:(unfold RtAPI.A_SSP_GUARD; lia))
    as (GOTm & can & CANm).
  (* 5. the walk *)
  pose proof SSW.strstr_wrap_holds as K. unfold SSWc.strstr_wrap_contract in K.
  specialize (K (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
                (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
                (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
                (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)
                fp_regs fp_csr mc st hs sw ((spZ regs) - 2 * ESTACK) can).
  cbv zeta in K. rewrite HX, HY in K. change (bv_unsigned (getr regs 2)) with (spZ regs) in K.
  assert (WALK : LX.evt IM.rsegs
      (SSWc.strstr_wrap_post (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 8) (getr regs 9)
         (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
         (getr regs 25) (getr regs 26) (getr regs 27) fp_regs fp_csr (getr regs 10) (getr regs 11) st hs sw
         ((spZ regs) - 2 * ESTACK) mc)
      (LS.MS (LF.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
                (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
                (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
                (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31))
          fp_regs (Z_to_bv 64 SWc.STRSTR_WRAP) fp_csr None mc (LP.seg_rom IM.rsegs))).
  { apply K.
    - (* haystack bytes, NUL, slack *)
      pose proof (Z.mod_pos_bound (x + astr_len st) 8 ltac:(lia)) as HM8.
      apply bytes_at_cleanL; [exact ROMEQ | rewrite length_app; cbn [length]; lia | exact BXm].
    - exact (proj2 SX).
    - rewrite <- EX. exact SLK.
    - lia.
    - apply bytes_at_cleanL; [exact ROMEQ | rewrite length_app; cbn [length]; lia | exact BYm].
    - exact (proj2 SY).
    - exact (AMC.mem_inv_of_bz mc (mem_inv_clean m)).
    - apply bytes_at_cleanL; [exact ROMEQ | rewrite LM.length_le8; unfold SWc.GOT_GUARD; lia |].
      exact GOTm.
    - apply bytes_at_cleanL; [exact ROMEQ | rewrite LM.length_le8; unfold SWc.GUARD; lia |].
      exact CANm.
    - lia.
    - lia.
    - apply (addressable_cleanL m _ _ ROMEQ). apply addressable_of_view; [lia | lia | unfold ART.APPMEM_END; lia | |].
      + intros i Hi. apply (app_of_amem x (astr_len st + 8)); [lia | exact AMX | lia].
      + exact XRA.
    - apply (addressable_cleanL m _ _ ROMEQ). apply addressable_of_view; [lia | lia | unfold ART.APPMEM_END; lia | |].
      + intros i Hi. apply (app_of_amem y (astr_len sw + 8)); [lia | exact AMY | lia].
      + exact YRA.
    - right. apply (app_of_amem x (astr_len st + 8)); [lia | exact AMX | lia].
    - right. apply (app_of_amem y (astr_len sw + 8)); [lia | exact AMY | lia].
    - intros i Hi. replace (x + i + 7) with (x + (i + 7)) by lia.
      apply (app_of_amem x (astr_len st + 8)); [lia | exact AMX | lia].
    - intros i Hi. replace (y + i + 7) with (y + (i + 7)) by lia.
      apply (app_of_amem y (astr_len sw + 8)); [lia | exact AMY | lia].
    - destruct (RtBzAdapt.sep_of_read (2 * ESTACK) W regs mem x (astr_len st + 1)
                  ltac:(unfold ESTACK; lia) ltac:(lia) RDX) as [SL|SR]; [left | right; exact SR].
      unfold ESTACK in SL.
      pose proof (round_sep (x + astr_len st) (spZ regs) HAL ltac:(lia)) as RS.
      unfold SWc.STRSTR_WRAP_K. rewrite LHS. rewrite <- EX. lia.
    - destruct (RtBzAdapt.sep_of_read (2 * ESTACK) W regs mem y (astr_len sw + 1)
                  ltac:(unfold ESTACK; lia) ltac:(lia) RDY) as [SL|SR]; [left | right; exact SR].
      unfold SWc.STRSTR_WRAP_K, ESTACK in *. rewrite <- EY. lia.
    - apply (stk_cleanL m (spZ regs - 2 * ESTACK) (spZ regs)); [unfold TFIB_IMG_END, ESTACK in *; lia | lia |].
      exact ST0.
    - unfold SWc.STRSTR_WRAP_K, ESTACK. lia.
    - unfold ART.HIGHMEM_BEG, ESTACK in *. lia.
    - unfold ART.APPMEM_END. lia.
    - exact (asan_cells_of_ARm B TB ly S (w_H W) mem ROMEQ (proj1 HAR)).
    - unfold TWA.shv2. rewrite HX, HY. rewrite <- EX, <- EY.
      split; (apply (shvis_cleanL m); [exact ROMEQ | lia | lia | apply shvis_of_hull]).
      + apply XHV. lia.
      + apply YHV. lia.
    - cellc B TB ROMEQ (proj1 HAR).
    - cellc B TB ROMEQ (proj1 HAR).
    - cellc B TB ROMEQ (proj1 HAR).
    - cellc B TB ROMEQ (proj1 HAR).
    - cellc B TB ROMEQ (proj1 HAR).
    - cellc B TB ROMEQ (proj1 HAR).
    - cellc B TB ROMEQ (proj1 HAR).
    - cellc B TB ROMEQ (proj1 HAR).
    - cellc B TB ROMEQ (proj1 HAR).
    - cellc B TB ROMEQ (proj1 HAR). }
  (* 6. the run, on the cleaned store, as a Bz walk *)
  eapply (bz_run_clean B TB W SegRtPC.PC_strstr regs mem md _ _
            (RtBzAdapt.romN_of_rt B W mem HROM) (RtBzAdapt.rom_viewO_of_ARm B TB ly S W mem (proj1 HAR))).
  - eapply RtBzAdaptP.evt_grows. apply RtBzClean.lib_evt_bz. exact WALK.
  - intros msc ms' model' (HQ & GROW) Hcl Heqv Hsbm _.
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                    E0 & MU & WM & MI & ST & AC & SH & BH' & BN').
    assert (EM : ms_mem msc = m') by (rewrite E0; reflexivity).
    assert (MOUT : forall w : word, ~ ((spZ regs) - 4608 <= bv_unsigned w < (spZ regs)) -> ms_mem msc w = clean m w).
    { intros w Hw. rewrite EM. apply MU. cbn [LF.outside]. split; [|exact I].
      rewrite SPE. unfold SWc.STRSTR_WRAP_K. lia. }
    assert (MIN : forall a, (spZ regs) - 4608 <= a < (spZ regs) -> ms_mem msc (Z_to_bv 64 a) <> None).
    { intros a Ha E. rewrite EM in E.
      destruct ST as (_ & _ & STA). rewrite SPE in STA. destruct (STA a ltac:(unfold ESTACK; lia)) as (_ & b & Hb).
      unfold LM.mrd, LM.wa in Hb. rewrite E in Hb.
      pose proof (seg_rom_none_high a ltac:(unfold TFIB_IMG_END, ESTACK in *; lia)) as N.
      change (seg_rom tfibsegs (Z_to_bv 64 a)) with (LP.seg_rom IM.rsegs (Z_to_bv 64 a)) in N.
      rewrite N in Hb. discriminate. }
    apply (RtBzAdaptP.art_post_ro_clean B LAWS (2 * ESTACK) 4608 ly S W regs mem md _ msc ms' model' HPRE
             ltac:(unfold ESTACK; lia) Hcl Heqv Hsbm).
    all: subst msc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + keep_regs.
    + exact MOUT.
    + exact MIN.
    + exact GROW.
    + intros regs' mem' HR _. cbv beta.
      assert (A10 : getr regs' 10%bv = Z_to_bv 64 (SST.strstr_val x st sw))
        by (rewrite (HR 10%bv), <- HX; reflexivity).
      rewrite A10.
      destruct (strstr_val_spec x st sw) as [(V0 & NO) | (j & FO & Vj)].
      * left. split; [rewrite V0; reflexivity | exact NO].
      * right. exists j. split; [exact FO | rewrite Vj; reflexivity].
Qed.

End s.

(* ---- the closing form: AR_laws discharged by the core's law proof, the record SegBSyms B the one residual ---- *)
Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : SegBSyms B.

Theorem seg_strstr_closed :
  RtSeg.astrstr_realizes tfibsegs B SegRtPC.PC_strstr RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof. exact (seg_strstr B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

End closed.

Print Assumptions seg_strstr_closed.
