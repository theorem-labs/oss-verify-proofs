(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/RepVsncf.v (commit 4d286b2e618d, file sha256 ba5d6bd85d22) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 8 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets and list indices by the same stage map), 0 list indices re-picked, and 3 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepVsncf.v (commit f01d79f3fb5, cf refill round 3; file sha256 ba87712ac280) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 8 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code except at the by-hand acceptances named below (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 1 pair(s) carry a BY-HAND acceptance (the internal file accept.tsv, re-measured each run): _ZN11__sanitizer9VSNPrintfEPciPKcPv+0x1c0 (data-differs: ACCEPTED by hand: jump table (33 entries, each the same VSNPrintf+off on both images))), and 4 pcs named in comments; 8 hand maps (the internal file resolve-run-f01d79f3fb5.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, the class-full report walk, slice F3): __sanitizer::VSNPrintf (0x6795c,
   with AppendNumber 0x6891c and internal_memset 0x64ba4) for the two formats of PopulateFreeArray's class-full arm,
   into Printf's 400-byte buffer: [vsn_ok : RepIFcf.vsn_spec_cf].
   rule 24: proves function __sanitizer::VSNPrintf (reuse search: ossv proof index v5 2026-10-30T01:54:20Z over the
   main, recipes, candidates and release trees + lemma index + live heads, `proof-index VSNPrintf Printf
   SharedPrintfCode AppendNumber AppendToErrorMessageBuffer MmapOrDie` 2026-10-30T02:25:54Z exit 0: every
   cgif_file_fuzzer line is an address-table line (YB1q / YB1w / YB1w); AGih.v (removed in this series) / AGii.v (removed in this series) hold states, no contract).

   The proof is one generic lemma [vsn_case] over the case's format, line, va_list slots and read-only regions: the
   seed (RepVsnD.vseed) is st_ok at the call (section 2), the engine's run to the [ret] (0x67dec) is the case's
   boolean RepVsnD.vchk, and the [ret] step and the post follow from that check (section 3).  The two formats are
   RepVsnD.vchk1 and RepVsnD.vchk2 (31 classes, one vm_compute). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d YO0c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFl1 YFl3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import RepIFcf RepVsnD.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The checks' meaning.                                                                                           *)
Lemma zall_disjb_sound : forall a l, forallb (zdisjb a) l = true -> zall_disjoint a l.
Proof.
intros a l. induction l as [|b l IH]; cbn [forallb zall_disjoint]; intros H; [exact I|].
apply andb_prop in H as [Hb H]. split; [|exact (IH H)].
unfold zdisjb in Hb. unfold zdisj. apply orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.
Lemma zpw_disjb_sound : forall l, zpw_disjb l = true -> zpairwise_disjoint l.
Proof.
induction l as [|a l IH]; cbn [zpw_disjb zpairwise_disjoint]; intros H; [exact I|].
apply andb_prop in H as [H1 H2]. split; [exact (zall_disjb_sound a l H1) | exact (IH H2)].
Qed.
Lemma rom_ok_each : forall rom, rom_ok rom = true -> forall r, In r rom ->
  YP09.r_base r = None /\ TFIB_IMG_LO <= YP09.r_lo r /\ YP09.r_hi r <= TFIB_IMG_END /\ YP09.r_whi r <= YP09.r_wlo r.
Proof.
intros rom H r Hr. unfold rom_ok in H. apply andb_prop in H as [H _]. rewrite forallb_forall in H.
specialize (H r Hr). cbv beta in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H2, H3, H4. split; [|lia].
revert H1. destruct (YP09.r_base r); cbn [YP09.obase_eqb]; intros X; [discriminate X | reflexivity].
Qed.
Lemma rom_ext : forall E rom, rom_ok rom = true ->
  map (extent_of_region E) rom = map (fun r => (YP09.r_lo r, YP09.r_hi r)) rom.
Proof.
intros E rom H. apply map_ext_in. intros r Hr. destruct (rom_ok_each rom H r Hr) as (Hb & _).
unfold extent_of_region. rewrite Hb. cbn [base_val]. f_equal; lia.
Qed.
Lemma rom_pw : forall E rom, rom_ok rom = true -> zpairwise_disjoint (map (extent_of_region E) rom).
Proof.
intros E rom H. rewrite (rom_ext E rom H). apply zpw_disjb_sound. unfold rom_ok in H. apply andb_prop in H as [_ H]. exact H.
Qed.
Lemma rom_hi : forall E rom x, rom_ok rom = true -> TFIB_IMG_END <= fst x -> zall_disjoint x (map (extent_of_region E) rom).
Proof.
intros E rom x H Hx. rewrite (rom_ext E rom H).
assert (A : forall r, In r rom -> YP09.r_hi r <= TFIB_IMG_END) by (intros r Hr; apply (rom_ok_each rom H r Hr)).
clear H. induction rom as [|r rom IH]; cbn [map zall_disjoint]; [exact I|]. split.
- unfold zdisj. cbn [fst snd]. right. pose proof (A r (or_introl eq_refl)). lia.
- apply IH. intros r' Hr'. apply A. right. exact Hr'.
Qed.
Lemma rom_win : forall E rom b wlo whi a, rom_ok rom = true ->
  In (b, wlo, whi) (windows rom) -> ~ (base_val E b + wlo <= a < base_val E b + whi).
Proof.
intros E rom b wlo whi a H Hin Ha. unfold windows in Hin. apply in_map_iff in Hin as (r & Heq & Hr).
injection Heq as <- <- <-. destruct (rom_ok_each rom H r Hr) as (_ & _ & _ & Hw). lia.
Qed.
Lemma chunk_has_sound : forall cs off v, chunk_has cs off v = true ->
  exists j, nth_error cs j = Some (YP09.mkChunk off (CVal 1 (SLit v))) /\ 0 <= v < 256.
Proof.
intros cs off v H. unfold chunk_has in H. apply existsb_exists in H as (c & Hc & Hb).
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in Hb. apply andb_prop in Hb as [Ho Hb]. apply Z.eqb_eq in Ho. subst co.
destruct cv as [w x| | |]; cbn iota in Hb; try discriminate Hb.
destruct x; cbn iota in Hb; try discriminate Hb.
apply andb_prop in Hb as [Hb Hr2]. apply andb_prop in Hb as [Hb Hr1]. apply andb_prop in Hb as [Hw Hx].
apply N.eqb_eq in Hw. apply Z.eqb_eq in Hx. apply Z.leb_le in Hr1. apply Z.ltb_lt in Hr2. subst.
destruct (In_nth_error _ _ Hc) as [j Hj]. exists j. split; [exact Hj | lia].
Qed.
Lemma wins_eqb_sound : forall l l', wins_eqb l l' = true -> l = l'.
Proof.
induction l as [|t l IH]; intros [|u l'] H; cbn [wins_eqb] in H; try discriminate H; [reflexivity|].
apply andb_prop in H as [H1 H2]. rewrite (win_eqb_eq t u H1), (IH l' H2). reflexivity.
Qed.
Lemma vrom_ok : forall E (m : word -> option byte) a bs,
  ro_bytes m a bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  forallb (fun v => (0 <=? v) && (v <? 256)) bs = true -> region_ok tfibsegs E m (vrom a bs).
Proof.
intros E m a bs HB Ha Hh Hr. unfold region_ok, vrom.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_map. apply Forall_forall. intros i Hi. apply in_seq in Hi.
rewrite forallb_forall in Hr. pose proof (Hr (nth i bs 0) (@nth_In Z i bs 0 ltac:(lia))) as Hv. cbv beta in Hv.
apply andb_prop in Hv as [Hv1 Hv2]. apply Z.leb_le in Hv1. apply Z.ltb_lt in Hv2.
eapply (chunk_ok_val tfibsegs E m 0 (a + Z.of_nat i) 1 (SLit (nth i bs 0)) (nth i bs 0));
[reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
rewrite Z.add_0_l. exact (HB i ltac:(lia)).
Qed.
Lemma forallb_app_l : forall {X} (f : X -> bool) l l', forallb f (l ++ l') = true -> forallb f l = true.
Proof. intros X f l l' H. rewrite forallb_app in H. apply andb_prop in H. exact (proj1 H). Qed.
Lemma forallb_app_r : forall {X} (f : X -> bool) l l', forallb f (l ++ l') = true -> forallb f l' = true.
Proof. intros X f l l' H. rewrite forallb_app in H. apply andb_prop in H. exact (proj2 H). Qed.
(* the alias fact of the seed: (240 | (sp - 456)) & 15 = 8 for a 16-aligned sp *)
Lemma ms_al_val : forall E, bv_unsigned (ew E 2) mod 16 = 0 -> sv_denot E MS_AL = sv_denot E (SLit 8).
Proof.
intros E H. apply bv_eq. unfold MS_AL. cbn [sv_denot]. rewrite alu64_and, alu64_or.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (240 mod 2 ^ 64) with 240. change (15 mod 2 ^ 64) with 15. change (8 mod 2 ^ 64) with 8.
rewrite Z.land_lor_distr_l. change (Z.land 240 15) with 0. rewrite Z.lor_0_l.
change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16.
change (2 ^ 64) with (2 ^ 60 * 16). rewrite Zaux.Zmod_mod_mult by lia. rewrite Zplus_mod, H. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The call state and the seed.                                                                                   *)
Section g.
Variables (W : world tfibsegs) (ly : alayout) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf va : Z).
#[local] Notation Hd := (w_H W).
#[local] Notation m0 := (mrestrict (w_H W) mem).
#[local] Notation sp := (bv_unsigned (getr regs 2%bv)).
Hypotheses (LY : layout_ok ly) (R10 : getr regs 10%bv = w64 buf) (R11 : getr regs 11%bv = w64 400)
  (R13 : getr regs 13%bv = w64 va) (Hra : YK0s.ret_ok (getr regs 1%bv)).
Hypotheses (Hsp16 : sp mod 16 = 0) (Hsplo : ly_stk_lo ly <= sp - VSN_STK)
  (P_stk : forall a, sp - VSN_STK <= a < sp -> apresent Hd mem a)
  (Hbsp : sp <= buf) (Hbhi : buf + 400 <= ly_stk_hi ly) (P_buf : forall a, buf <= a < buf + 400 -> apresent Hd mem a)
  (Hvb : va + 24 <= buf \/ buf + 400 <= va) (Hvsp : sp <= va) (Hvhi : va + 24 <= ly_stk_hi ly).
Lemma zone_facts : kHighMemBeg + VSN_STK <= sp /\ buf + 400 <= kHighMemEnd /\ va + 24 <= kHighMemEnd.
Proof.
pose proof (lo_top ly LY) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
clear - A1 A2 A4 A7 Hsplo Hbsp Hbhi Hvsp Hvhi. unfold VSN_STK in *. lia.
Qed.
Ltac zf := pose proof zone_facts as (Z1 & Z2 & Z3); pose proof (u64_range (getr regs 2%bv)) as Z0;
  unfold VSN_STK, kHighMemBeg, kHighMemEnd, TFIB_IMG_END in *.
Definition E0 : env := Ereg regs [].
Lemma E1 : ew E0 1 = getr regs 1%bv. Proof. exact (ew_Ereg_nat regs [] 1 1%bv eq_refl). Qed.
Lemma E2 : ew E0 2 = getr regs 2%bv. Proof. exact (ew_Ereg_nat regs [] 2 2%bv eq_refl). Qed.
Lemma E10 : bv_unsigned (ew E0 10) = buf.
Proof.
unfold E0. rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl), R10. unfold w64. apply unsigned_lit_small. zf. lia.
Qed.
Lemma E13 : bv_unsigned (ew E0 13) = va.
Proof.
unfold E0. rewrite (ew_Ereg_nat regs [] 13 13%bv eq_refl), R13. unfold w64. apply unsigned_lit_small. zf. lia.
Qed.
Lemma FACTS_ok : facts_ok E0 VFACTS.
Proof.
assert (AF : forall k X lo hi al, bv_unsigned (ew E0 k) = X -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 ->
  afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. repeat split; lia. }
unfold VFACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [| split; [exact I | split; [| exact I]]].
- split; [| split; [| split; [| exact I]]].
  + apply (AF 2%nat sp); [rewrite E2; reflexivity | zf; lia | exact Hsp16 | lia].
  + apply (AF 10%nat buf); [exact E10 | zf; lia | apply Z.mod_1_r | lia].
  + apply (AF 13%nat va); [exact E13 | zf; lia | apply Z.mod_1_r | lia].
- apply ms_al_val. rewrite E2. exact Hsp16.
Qed.
Lemma R_S_ok : region_ok tfibsegs E0 m0 R_S.
Proof.
unfold R_S. apply (region_ok_stack tfibsegs E0 m0 2 sp (- VSN_STK)); [rewrite E2; reflexivity | zf; lia | zf; lia |].
intros a Ha. apply YF0x.apresent_writable; [zf; lia | apply P_stk; lia].
Qed.
Lemma R_B_ok : forall n, 1 <= n <= 400 -> region_ok tfibsegs E0 m0 (R_B n).
Proof.
intros n Hn. unfold R_B. apply (region_ok_window E0 m0 10 buf); [exact E10 | zf; lia | zf; lia |].
intros a Ha. apply YF0x.apresent_writable; [zf; lia | apply P_buf; lia].
Qed.
Lemma R_VA_ok : forall vs, 8 * Z.of_nat (length vs) <= 24 ->
  (forall i, (i < length vs)%nat -> val_mem tfibsegs m0 (va + 8 * Z.of_nat i) 8 (nth i vs 0) /\ 0 <= nth i vs 0 < 2 ^ 64) ->
  region_ok tfibsegs E0 m0 (R_VA vs).
Proof.
intros vs Hl HV. unfold region_ok, R_VA.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E13.
split; [zf; lia|]. split; [zf; lia|]. split; [intros o Ho; lia|].
apply Forall_map. apply Forall_forall. intros i Hi. apply in_seq in Hi. destruct (HV i ltac:(lia)) as [Hv Hr].
eapply (chunk_ok_val tfibsegs E0 m0 va (8 * Z.of_nat i) 8 (SLit (nth i vs 0)) (nth i vs 0));
[reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hr | cbn; lia | exact Hv].
Qed.
#[local] Notation ms0 := (mkst regs (w64 A_VSNPRINTF) mem (seg_rom tfibsegs)).
Lemma SEED_ok : forall fmt n vs rom,
  getr regs 12%bv = w64 fmt -> 1 <= n <= 400 -> 8 * Z.of_nat (length vs) <= 24 ->
  (forall i, (i < length vs)%nat -> val_mem tfibsegs m0 (va + 8 * Z.of_nat i) 8 (nth i vs 0) /\ 0 <= nth i vs 0 < 2 ^ 64) ->
  Forall (region_ok tfibsegs E0 m0) rom -> rom_ok rom = true -> regions_wf (vmem n vs rom) = true ->
  st_ok tfibsegs E0 (vseed fmt n vs rom) (restrict Hd ms0).
Proof.
intros fmt n vs rom R12 Hn Hl HV HR HRO HWF. rewrite restrict_mkst_fx. unfold vseed, VREGS, w64.
apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R12].
  apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; exact R11].
- exact HWF.
- unfold vmem. apply Forall_cons; [exact R_S_ok|]. apply Forall_cons; [exact (R_B_ok n Hn)|].
  apply Forall_cons; [exact (R_VA_ok vs Hl HV) | exact HR].
- change (Ereg regs []) with E0. apply pairwise_disjoint_of_extents. unfold vmem. cbn [map].
  assert (ES : extent_of_region E0 R_S = (sp - VSN_STK, sp)).
  { unfold extent_of_region, R_S. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2. f_equal; lia. }
  assert (EB : extent_of_region E0 (R_B n) = (buf, buf + n)).
  { unfold extent_of_region, R_B. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E10. f_equal; lia. }
  assert (EV : extent_of_region E0 (R_VA vs) = (va, va + 8 * Z.of_nat (length vs))).
  { unfold extent_of_region, R_VA. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E13. f_equal; lia. }
  rewrite ES, EB, EV. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; try (apply rom_hi; [exact HRO | cbn [fst]; zf; lia]); try (apply rom_pw; exact HRO); zf; lia.
- exact FACTS_ok.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The run, the [ret], the post.                                                                                  *)
Definition VPOST (out : list Z) : world tfibsegs -> config -> Prop := fun W' c' =>
  W' = W /\ exists regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1%bv) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\ getr regs' 10%bv = w64 (Z.of_nat (length out)) /\
  (forall x : word, ~ (sp - VSN_STK <= bv_unsigned x < sp) ->
     ~ (buf <= bv_unsigned x <= buf + Z.of_nat (length out)) -> mem' x = mem x) /\
  (forall a, apresent Hd mem a -> apresent Hd mem' a) /\
  (forall i, (i < length out)%nat -> val_mem tfibsegs (mrestrict Hd mem') (buf + Z.of_nat i) 1 (nth i out 0)) /\
  val_mem tfibsegs (mrestrict Hd mem') (buf + Z.of_nat (length out)) 1 0.
Lemma seed_wins : forall n vs rom b wlo whi a, rom_ok rom = true ->
  In (b, wlo, whi) (windows (vmem n vs rom)) -> base_val E0 b + wlo <= a < base_val E0 b + whi ->
  (sp - VSN_STK <= a < sp) \/ (buf <= a < buf + n).
Proof.
intros n vs rom b wlo whi a HRO Hin Ha. unfold vmem, windows in Hin. cbn [map] in Hin.
destruct Hin as [Hq | [Hq | [Hq | Hin]]].
- unfold R_S in Hq. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hq. injection Hq as <- <- <-.
  cbn [base_val] in Ha. rewrite E2 in Ha. left. lia.
- unfold R_B in Hq. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hq. injection Hq as <- <- <-.
  cbn [base_val] in Ha. rewrite E10 in Ha. right. lia.
- unfold R_VA in Hq. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hq. injection Hq as <- <- <-. lia.
- exfalso. exact (rom_win E0 rom b wlo whi a HRO Hin Ha).
Qed.
Lemma vsn_case : forall fmt out vs rom,
  getr regs 12%bv = w64 fmt -> Z.of_nat (length out) < 400 -> 8 * Z.of_nat (length vs) <= 24 ->
  (forall i, (i < length vs)%nat -> val_mem tfibsegs m0 (va + 8 * Z.of_nat i) 8 (nth i vs 0) /\ 0 <= nth i vs 0 < 2 ^ 64) ->
  Forall (region_ok tfibsegs E0 m0) rom -> vchk fmt out vs rom = true ->
  SRr tfibsegs W (mkCfg ms0 md) (VPOST out).
Proof using All.
intros fmt out vs rom R12 Hlen Hl HV HR Hchk. unfold vchk in Hchk. cbv zeta in Hchk.
apply andb_prop in Hchk as [Hchk HRUN]. apply andb_prop in Hchk as [HWF HRO].
pose proof (SEED_ok fmt (Z.of_nat (length out) + 1) vs rom R12 ltac:(lia) Hl HV HR HRO HWF) as HS.
set (seed := vseed fmt (Z.of_nat (length out) + 1) vs rom) in *. unfold vrun in HRUN.
revert HRUN. destruct (sym_run_toN_sh tfibsegs tfibtbl_rtD YP03.FUEL A_VSN_RET seed) as [ssF st] eqn:Hrun.
destruct st; cbv beta iota; intros HRUN; try discriminate HRUN.
eapply (SRr_run_to_sh_gen tfibsegs tfibtbl_rtD tfibtbl_rtD_ok Hwx_tfa W YP03.FUEL A_VSN_RET E0 seed ssF RS_running
  ms0 md (VPOST out) HS Hrun).
intros ms' mat' HS' HF _. cbv beta iota in HS'. cbn [ms_mem mkst] in HF.
unfold vfin_ok in HRUN.
apply andb_prop in HRUN as [HRUN HBUF]. apply andb_prop in HRUN as [HRUN HWS].
apply andb_prop in HRUN as [HRUN HA0]. apply andb_prop in HRUN as [HRUN HRA].
apply andb_prop in HRUN as [HRUN HCS]. apply andb_prop in HRUN as [HPC HRV].
apply Z.eqb_eq in HPC. apply sv_eqb_eq in HA0, HRA. apply wins_eqb_sound in HWS.
assert (HRV' : ss_resv ssF = None).
{ revert HRV. destruct (ss_resv ssF); cbv beta iota; intros X; [discriminate X | reflexivity]. }
eapply (SRr_ret_at tfibsegs tfibtbl_rtD tfibtbl_rtD_ok Hwx_tfa W E0 ssF ms' _ _ HS' HRV');
[rewrite HPC; exact ret_word |].
intros mat''. rewrite wvb_collapse. unfold VPOST. split; [reflexivity|].
exists (ms_regs ms'), (ms_mem ms'), mat''.
assert (G : forall r, getr (ms_regs ms') r = sv_denot E0 (sr_get (ss_regs ssF) r))
  by (intros r; exact (st_ok_restrict_reg tfibsegs Hd E0 ssF ms' r HS')).
split.
{ rewrite G, HRA. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E1. unfold YK0s.ret_ok in Hra. rewrite Hra.
  reflexivity. }
split.
{ exact (regs_preserved_of_st_ok tfibsegs E0 ssF (restrict Hd ms') regs [] HS' (env_agree_refl 32 E0) HCS). }
split.
{ rewrite G, HA0. reflexivity. }
assert (HHI : forall a, in_wrange E0 (ss_mem seed) a ->
  (sp - VSN_STK <= a < sp) \/ (buf <= a < buf + (Z.of_nat (length out) + 1))).
{ intros a Ha. apply in_wrange_windows in Ha as (b & wlo & whi & Hin & Hb).
  exact (seed_wins _ vs rom b wlo whi a HRO Hin Hb). }
split.
{ intros x N1 N2. apply HF. intros Hin. destruct (HHI _ Hin) as [Hx|Hx]; [exact (N1 Hx) | apply N2; lia]. }
split.
{ intros a Ha. apply (pres_after_run Hd E0 ssF (ss_mem seed) ms0 ms' HS' HF HWS); [| exact Ha].
  intros a' Ha'. destruct (HHI a' Ha') as [Hx|Hx]; zf; lia. }
revert HBUF. destruct (nth_error (ss_mem ssF) 1) as [r|] eqn:Hr; cbv beta iota; intros HBUF; [| discriminate HBUF].
apply andb_prop in HBUF as [HB10 HBY]. rewrite forallb_forall in HBY.
assert (HBASE : base_val E0 (YP09.r_base r) = buf).
{ revert HB10. destruct (YP09.r_base r) as [k|]; cbn [YP09.obase_eqb base_val]; intros X; [| discriminate X].
  apply Nat.eqb_eq in X. subst k. exact E10. }
assert (BY : forall i, (i <= length out)%nat ->
  val_mem tfibsegs (mrestrict Hd (ms_mem ms')) (buf + Z.of_nat i) 1 (nth i (out ++ [0]) 0)).
{ intros i Hi. destruct (chunk_has_sound _ _ _ (HBY i ltac:(apply in_seq; lia))) as (j & Hj & Hv).
  rewrite <- HBASE.
  exact (st_ok_chunk_val Hd E0 ssF ms' 1%nat r j (Z.of_nat i) 1%N (SLit _) _ HS' Hr Hj eq_refl Hv ltac:(cbn; lia)). }
split.
{ intros i Hi. rewrite <- (app_nth1 out [0] 0 Hi). apply BY. lia. }
pose proof (BY (length out) (le_n _)) as X. rewrite nth_middle in X. exact X.
Qed.
End g.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The theorem.                                                                                                   *)
Lemma rom1_ok : forall E (m : word -> option byte), vsn_img_facts m -> Forall (region_ok tfibsegs E m) ROM1.
Proof.
intros E m [F1 F2 F3 F4 F5]. pose proof rom_bytes_range as B.
unfold ROM1, ROM_JT, vlit4, JT_S, JT_U.
apply Forall_cons; [apply vrom_ok; [exact F1 | unfold FMT_OOM1; lia | vm_compute; intros X; discriminate X
  | exact (forallb_app_l _ _ _ B)]|].
apply Forall_cons; [apply vrom_ok; [exact F3 | unfold A_TOOLNAME; lia | vm_compute; intros X; discriminate X
  | exact (forallb_app_r _ _ _ (forallb_app_r _ _ _ B))]|].
apply Forall_cons; [exact (region_ok_lit E m 0x20cd4 4 0x46ef0 F4 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))|].
apply Forall_cons; [exact (region_ok_lit E m 0x20cdc 4 0x46ec8 F5 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))|].
apply Forall_nil.
Qed.
Lemma rom2_ok : forall E (m : word -> option byte), vsn_img_facts m -> Forall (region_ok tfibsegs E m) ROM2.
Proof.
intros E m [F1 F2 F3 F4 F5]. pose proof rom_bytes_range as B.
unfold ROM2, ROM_JT, vlit4, JT_S, JT_U.
apply Forall_cons; [apply vrom_ok; [exact F2 | unfold FMT_OOM2; lia | vm_compute; intros X; discriminate X
  | exact (forallb_app_l _ _ _ (forallb_app_r _ _ _ B))]|].
apply Forall_cons; [exact (region_ok_lit E m 0x20cd4 4 0x46ef0 F4 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))|].
apply Forall_cons; [exact (region_ok_lit E m 0x20cdc 4 0x46ec8 F5 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))|].
apply Forall_nil.
Qed.
Lemma class_size_word : forall c, 1 <= c <= 31 -> 0 <= class_size c < 2 ^ 64.
Proof.
intros c Hc.
assert (A : forallb (fun c => (0 <=? class_size c) && (class_size c <? 2 ^ 64)) (map Z.of_nat (seq 1 31)) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in A.
specialize (A c ltac:(apply in_map_iff; exists (Z.to_nat c); split; [lia | apply in_seq; lia])). cbv beta in A.
apply andb_prop in A as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2. lia.
Qed.
Theorem vsn_ok : vsn_spec_cf.
Proof.
unfold vsn_spec_cf. intros W ly regs mem md buf fmt va out. cbv zeta.
intros LY IMG R10 R11 R12 R13 R4 Hra FC VIF Hlen Hsp16 Hsplo P_stk Hbsp Hbhi P_buf Hvb Hvsp Hvhi.
destruct FC as [(-> & HV & ->) | (c & sz & -> & Hc & -> & HV1 & HV2 & HV3 & ->)].
- apply (vsn_case W ly regs mem md buf va LY R10 R11 R13 Hra Hsp16 Hsplo P_stk Hbsp Hbhi P_buf Hvb Hvsp Hvhi
    FMT_OOM1 render1 [A_TOOLNAME] ROM1 R12 Hlen ltac:(cbn; lia)).
  + intros i Hi. destruct i as [|i]; [| cbn in Hi; lia]. cbn [nth].
    split; [replace (va + 8 * Z.of_nat 0) with va by lia; exact HV | unfold A_TOOLNAME; lia].
  + exact (rom1_ok _ _ VIF).
  + exact vchk1.
- pose proof (class_size_word c Hc) as SZ.
  apply (vsn_case W ly regs mem md buf va LY R10 R11 R13 Hra Hsp16 Hsplo P_stk Hbsp Hbhi P_buf Hvb Hvsp Hvhi
    FMT_OOM2 (render2 c (class_size c)) [REGION_MB; c; class_size c] ROM2 R12 Hlen ltac:(cbn; lia)).
  + intros i Hi. destruct i as [|[|[|i]]]; cbn [nth]; [| | | cbn in Hi; lia].
    * split; [replace (va + 8 * Z.of_nat 0) with va by lia; exact HV1 | unfold REGION_MB; lia].
    * split; [replace (va + 8 * Z.of_nat 1) with (va + 8) by lia; exact HV2 | lia].
    * split; [replace (va + 8 * Z.of_nat 2) with (va + 16) by lia; exact HV3 | exact SZ].
  + exact (rom2_ok _ _ VIF).
  + exact (vchk2 c Hc).
Qed.
End e.
