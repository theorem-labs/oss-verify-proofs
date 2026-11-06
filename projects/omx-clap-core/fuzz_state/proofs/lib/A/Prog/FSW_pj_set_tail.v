(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v, with its module paths and module names changed; 1342 of its 1436 lines of code are new or changed and 2592 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/Prog/FSW_pj_set_holds.v; 289 of its 359 lines of code are new or changed and 1366 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/Prog/FSW_pj_set_rt.v; 223 of its 263 lines of code are new or changed and 319 lines of the source are left out. *)
(* The TAIL of pj_set's ASan walk (fs.asan, pj_set 0x838e8, pf.c:384-391): from the resume state after fuzz_strdup
   (0x83998, stage D's entry ss_pD0) through stage D, the __asan_memcpy (kids + 56 n, val, 56) call, stage E, the
   __asan_memset (val, 0, 56) call and stage F to pj_set's `ret`, closed as FSH_Gen.fpostU. Pure composition of the
   Qed stages (FSW_pj_set.v pj_set_stageD / E / F), the runtime calls (FSW_pj_set_rt.v pS_memcpy_call /
   pS_memset_call) and FSW_ret.fsw_retU, plus the memory carries of val's pobj below: across stage D (its memory moves
   only on the keys[n] slot and obj's written fields, both apart from val and off the shadow: pSt_pobj_frame), across
   the memcpy (its view moves only on the destination and on the callee's stack window above alloc_ceiling, presence
   kept: pSt_pobj_rt) and across stage E (FSW_rd.pobj_below). For a Theorem Labs lane's FSW_pj_set_holds.v, which imports this
   file. rule 24: pj_set proved new (a Theorem Labs lane's lookup, CONFIRM a Theorem Labs lane 04:16Z). A lemma file: no function
   contract is proved here. *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_ret FSW_pj FSW_K3 FSW_rd FSW_rres FSPstat FSH_Fn_reader FSH_Fn_alloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require Import FSW_pj_set_tbl FSW_pj_set FSW_pj_set_rt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the callee-saved registers stage F keeps are callee-saved for aregs_preserved *)
Lemma pSt_cs : forall r : bv 5, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [unfold acallee_saved; vm_compute;
  first [lia | right; right; right; right; right; split; first [exact I | congruence | discriminate]] |]).
destruct Hr.
Qed.

Section TL. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis RT_memcpy : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis RT_memset : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.

(* a byte below alloc_ceiling has its shadow byte below alloc_ceiling, inside the shadow *)
Lemma pSt_shadow : forall x, 0 <= x < alloc_ceiling ->
  0 <= shadow_of_addr SHADOW_OFF x < alloc_ceiling /\
  SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 2 ^ 44.
Proof.
intros x Hx. pose proof asan_consts as (C1 & _).
split; [exact (fsw_shadow_below x Hx)|].
unfold shadow_of_addr. Z.div_mod_to_equations. lia.
Qed.
(* ---- the carries of a pobj (FSH_Fn_reader.pobj) to another memory ---- *)
(* a pobj stays one when the view of its shadow bytes and its writability are kept *)
Lemma pSt_pobj_carry : forall ly S (W : world tfibsegs) m m' v,
  pobj tfibsegs B ly S W m v ->
  (forall x, v <= x < v + 56 ->
     aview tfibsegs (w_H W) m' (shadow_of_addr SHADOW_OFF x) = aview tfibsegs (w_H W) m (shadow_of_addr SHADOW_OFF x)) ->
  (forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W) m') (v + i)) ->
  pobj tfibsegs B ly S W m' v.
Proof.
intros ly S W m m' v (Hpl & _) HA Hw. split; [|exact Hw].
assert (RA : range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF v 56 ->
  range_addressable (aview tfibsegs (w_H W) m') SHADOW_OFF v 56).
{ intros Hr x Hx. destruct (Hr x Hx) as (s & Es & Hok). exists s. split; [|exact Hok]. rewrite (HA x Hx). exact Es. }
destruct Hpl as [(Hf & Ha & Hr)|(Hb & Ha & Hr)]; [left | right].
- split; [exact Hf|]. split; [exact Ha | exact (RA Hr)].
- split; [exact Hb|]. split; [exact Ha | exact (RA Hr)].
Qed.
(* across a memory change that keeps every byte below alloc_ceiling off a set P of non-shadow bytes apart from v
   (stage D: P = the keys[n] slot and obj's written fields) *)
Lemma pSt_pobj_frame : forall ly S (W : world tfibsegs) mx md m m' v (P : Z -> Prop),
  AR tfibsegs B ly S W mx md -> pobj tfibsegs B ly S W m v ->
  (forall x, 0 <= x < alloc_ceiling -> ~ P x -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  (forall x, v <= x < v + 56 -> ~ P x) ->
  (forall x, P x -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44)) ->
  pobj tfibsegs B ly S W m' v.
Proof.
intros ly S W mx md m m' v P HAR HP HM Hv Hsh.
destruct (fsw_pobj_low B ly S W mx md m v HAR HP) as (L1 & L2).
apply (pSt_pobj_carry ly S W m m' v HP).
- intros x Hx. destruct (pSt_shadow x ltac:(lia)) as (S1 & S2).
  apply (aview_at tfibsegs). apply HM; [exact S1|]. intros Hp. exact (Hsh _ Hp S2).
- intros i Hi. destruct HP as (_ & Hw).
  apply (writable_at_eq tfibsegs (mrestrict (w_H W) m)); [|exact (Hw i Hi)].
  unfold mrestrict. rewrite (HM (v + i)) by (first [lia | exact (Hv (v + i) ltac:(lia))]). reflexivity.
Qed.
(* across a runtime call that keeps the view off its destination d (no shadow byte) and off a window above
   alloc_ceiling, and keeps presence (pS_memcpy_call's post) *)
Lemma pSt_pobj_rt : forall ly S U (W : world tfibsegs) m md m' v d lo hi,
  ARU tfibsegs B ly S U W m md -> pobj tfibsegs B ly S W m v ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (d <= x < d + 56) -> ~ (lo <= x < hi) ->
     aview tfibsegs (w_H W) m' x = aview tfibsegs (w_H W) m x) ->
  (forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
  (forall x, d <= x < d + 56 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44)) ->
  alloc_ceiling <= lo ->
  pobj tfibsegs B ly S W m' v.
Proof.
intros ly S U W m md m' v d lo hi HARU HP HA HPr Hd Hlo.
pose proof asan_consts as (C1 & _).
destruct (fsw_pobj_low B ly S W (unpoison U m) md m v (ARU_AR tfibsegs B ly S U W m md HARU) HP) as (L1 & L2).
destruct (pSr_pobj B ly S W m v HP) as (HIN & _).
destruct (pSr_obj_facts B ly S U W m md v HARU HIN) as (_ & _ & _ & HPR & _).
apply (pSt_pobj_carry ly S W m m' v HP).
- intros x Hx. destruct (pSt_shadow x ltac:(lia)) as (S1 & S2).
  apply HA; [lia | intros Hy; exact (Hd _ Hy S2) | lia].
- intros i Hi. apply (apresent_writable tfibsegs). apply HPr. exact (proj1 (HPR (v + i) ltac:(lia))).
Qed.

(* ---- the tail: 0x83998 (after fuzz_strdup) .. pj_set's ret ---- *)
Lemma pS_tail : forall ly S U (W : world tfibsegs) regs mem md
    ly4 S4 U4 (W4 : world tfibsegs) regs4 mem4 md4 (k4 : Z) (FP : list (Z * Z))
    (cnt fail live peak kids keys n cap o w a : Z)
    (Qf : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  let slot := keys + 8 * n in
  let dst := kids + 56 * n in
  YK0s.ret_ok (YK11.getr regs 1) ->
  YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  ajournal tfibsegs B STK_pj_set (spZ regs) FP ly S W (unpoison U mem) md [] ly4 S4 W4 (unpoison U4 mem4) md4 k4 ->
  ARU tfibsegs B ly4 S4 U4 W4 mem4 md4 ->
  FSupoisonU.fs_heads B ly4 S4 U4 ->
  st_ok tfibsegs (Ereg regs4 (fs_extraT ++ pj_xs cnt fail live peak 6 kids keys n cap regs)) ss_pD0
    (restrict (w_H W4) (mkst regs4 (Z_to_bv 64 0x83998) mem4 (seg_rom tfibsegs))) ->
  spZ regs4 = spZ regs - 48 ->
  YK11.getr regs4 9 = w64 o -> YK11.getr regs4 8 = w64 w -> YK11.getr regs4 10 = w64 a ->
  YK11.getr regs4 20 = w64 SHADOW_OFF ->
  Forall (fun r => YK11.getr regs4 r = YK11.getr regs r) [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv ->
  pobj tfibsegs B ly4 S4 W4 mem4 o -> pobj tfibsegs B ly4 S4 W4 mem4 w ->
  4096 + HEAD <= a < 2 ^ 47 -> a mod 16 = 0 ->
  0 <= keys < 2 ^ 64 -> 0 <= n -> 0 <= kids -> 0 <= cap < 2 ^ 64 ->
  (exists p nn, In (p, nn) (ablocks B ly4 S4) /\ p + HEAD <= slot /\ slot + 8 <= p + req_size nn) ->
  slot mod 8 = 0 ->
  (exists p nn, In (p, nn) (ablocks B ly4 S4) /\ p + HEAD <= dst /\ dst + 56 <= p + req_size nn) ->
  (slot + 8 <= o \/ o + 56 <= slot) -> (slot + 8 <= w \/ w + 56 <= slot) ->
  (dst + 56 <= o \/ o + 56 <= dst) -> (dst + 56 <= w \/ w + 56 <= dst) ->
  (dst + 56 <= slot \/ slot + 8 <= dst) -> (w + 56 <= o \/ o + 56 <= w) ->
  (forall x, slot <= x < slot + 8 ->
     awr_byte tfibsegs B STK_pj_set (spZ regs) FP (ablocks B ly S) (ablocks B ly4 S4) ly4 [] (frames S) x) ->
  (forall x, o + 24 <= x < o + 56 ->
     awr_byte tfibsegs B STK_pj_set (spZ regs) FP (ablocks B ly S) (ablocks B ly4 S4) ly4 [] (frames S) x) ->
  (forall x, dst <= x < dst + 56 ->
     awr_byte tfibsegs B STK_pj_set (spZ regs) FP (ablocks B ly S) (ablocks B ly4 S4) ly4 [] (frames S) x) ->
  (forall x, w <= x < w + 56 ->
     awr_byte tfibsegs B STK_pj_set (spZ regs) FP (ablocks B ly S) (ablocks B ly4 S4) ly4 [] (frames S) x) ->
  (forall m5 m6 m6' m7 regsF memF mdF,
     val_mem tfibsegs (mrestrict (w_H W4) m5) slot 8 a ->
     val_mem tfibsegs (mrestrict (w_H W4) m5) (o + 24) 8 kids ->
     val_mem tfibsegs (mrestrict (w_H W4) m5) (o + 32) 8 keys ->
     val_mem tfibsegs (mrestrict (w_H W4) m5) (o + 40) 8 (n + 1) ->
     val_mem tfibsegs (mrestrict (w_H W4) m5) (o + 48) 8 cap ->
     (forall x, 0 <= x < alloc_ceiling -> ~ (slot <= x < slot + 8) -> ~ (o + 24 <= x < o + 56) ->
        m5 (Z_to_bv 64 x) = mem4 (Z_to_bv 64 x)) ->
     (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W4) m6 (dst + i) = aview tfibsegs (w_H W4) m5 (w + i)) ->
     (forall x, 0 <= x < alloc_ceiling -> ~ (dst <= x < dst + 56) ->
        aview tfibsegs (w_H W4) m6 x = aview tfibsegs (w_H W4) m5 x) ->
     same_below m6 m6' alloc_ceiling ->
     (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W4) m7 (w + i) = Some 0) ->
     (forall x, 0 <= x < alloc_ceiling -> ~ (w <= x < w + 56) ->
        aview tfibsegs (w_H W4) m7 x = aview tfibsegs (w_H W4) m6' x) ->
     same_below m7 memF alloc_ceiling ->
     YK11.getr regsF 10 = w64 0 ->
     Qf ly4 S4 W4 regsF memF mdF) ->
  SRr tfibsegs W4 (mkCfg (mkst regs4 (Z_to_bv 64 0x83998) mem4 (seg_rom tfibsegs)) md4)
    (fpostU tfibsegs B STK_pj_set (spZ regs) FP regs ly S U W mem md k4 U4 Qf).
Proof.
intros ly S U W regs mem md ly4 S4 U4 W4 regs4 mem4 md4 k4 FP cnt fail live peak kids keys n cap o w a Qf slot dst
  Hra R3 R4 HJ HARU FH HS Hsp R9 R8 R10 R20 Hkeep HPo HPw Ha Ha16 Hk Hn Hki Hcap HSB Hs8 HDB
  Dso Dsw Ddo Ddw Dds Dwo WS WO WD WW KQ.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & _).
pose proof (ARU_AR tfibsegs B ly4 S4 U4 W4 mem4 md4 HARU) as HAR4.
assert (Eslot : slot = keys + 8 * n) by reflexivity.
assert (Edst : dst = kids + 56 * n) by reflexivity.
assert (S48 : 48 <= STK_pj_set) by (vm_compute; congruence).
assert (SE48 : ESTACK + 48 <= STK_pj_set) by (vm_compute; congruence).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
assert (Hwin : alloc_ceiling <= spZ regs - 48 - ESTACK) by lia.
(* ---- obj and val: below alloc_ceiling, off the shadow; obj 8-aligned and addressable ---- *)
destruct (fsw_pobj_low B ly4 S4 W4 (unpoison U4 mem4) md4 mem4 o HAR4 HPo) as (O1 & O2).
destruct (fsw_pobj_low B ly4 S4 W4 (unpoison U4 mem4) md4 mem4 w HAR4 HPw) as (Wl1 & Wl2).
assert (O8 : o mod 8 = 0) by (destruct HPo as ([(_ & X & _)|(_ & X & _)] & _); exact X).
destruct (pSr_pobj B ly4 S4 W4 mem4 o HPo) as (_ & ORA).
pose proof (fsw_pobj_off_shadow B ly4 S4 W4 (unpoison U4 mem4) md4 mem4 o HAR4 HPo) as OSH.
assert (Hw64 : 0 <= w < 2 ^ 64) by lia.
(* ---- the keys[n] slot and the kids[n] destination: inside live blocks past their heads ---- *)
pose proof HSB as (ps & nns & Hins & Hs1 & Hs2).
pose proof HDB as (pd & nnd & Hind & Hd1 & Hd2).
unfold HEAD in Hs1, Hd1.
destruct (fsw_ablock_low B ly4 S4 W4 (unpoison U4 mem4) md4 ps nns HAR4 Hins) as (P1 & P2 & _).
destruct (fsw_ablock_low B ly4 S4 W4 (unpoison U4 mem4) md4 pd nnd HAR4 Hind) as (Q1 & Q2 & _).
pose proof (fsw_ablock_off_img B ly4 S4 W4 (unpoison U4 mem4) md4 ps nns HAR4 Hins) as PIMG.
pose proof (fsw_ablock_off_shadow B ly4 S4 W4 (unpoison U4 mem4) md4 ps nns HAR4 Hins) as PSH.
pose proof (fsw_ablock_off_shadow B ly4 S4 W4 (unpoison U4 mem4) md4 pd nnd HAR4 Hind) as DSH0.
assert (Hkn : kids + 56 * n < 2 ^ 64) by lia.
assert (Hs4 : 4096 + HEAD <= slot) by (unfold HEAD; lia).
assert (Hsc : slot + 8 <= alloc_ceiling) by lia.
assert (SIMG : slot + 8 <= 0x10000 \/ FS_IMG_END <= slot) by (destruct PIMG; [left | right]; lia).
assert (SSH : forall x, slot <= x < slot + 8 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44))
  by (intros x Hx; apply PSH; lia).
assert (DSH : forall x, dst <= x < dst + 56 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44))
  by (intros x Hx; apply DSH0; lia).
assert (SWR : forall i, 0 <= i < 8 -> writable_at tfibsegs (mrestrict (w_H W4) mem4) (slot + i)).
{ intros i Hi.
  destruct (al_blocks _ _ LAWS ly4 S4 W4 (unpoison U4 mem4) md4 ps nns HAR4 Hins) as (_ & _ & _ & _ & Hb & _).
  assert (Hpi : ps <= slot + i < ps + req_size nns) by lia.
  assert (Hri : 0 <= slot + i < 2 ^ 64) by lia.
  apply (apresent_writable tfibsegs).
  exact (pSr_present_raw B ly4 S4 U4 W4 mem4 md4 (slot + i) HARU Hri (PSH _ Hpi) (proj1 (Hb _ Hpi))). }
assert (Hs16 : ps + 16 <= slot) by lia.
assert (Hl8 : 0 <= 8) by lia.
pose proof (fsw_block_body_addressable B ly4 S4 U4 W4 mem4 md4 ps nns slot 8 HARU FH Hins Hs16 Hl8 Hs2) as SRA.
(* ---- STAGE D: 0x83998 .. jal __asan_memcpy (kids + 56 n, val, 56) ---- *)
apply (pj_set_stageD B ly S W (unpoison U mem) md [] ly4 S4 U4 W4 regs regs4 mem4 md4 STK_pj_set (spZ regs) FP k4
  cnt fail live peak 6 kids keys n cap o w a _ HS HJ HARU Hsp S48 R9 R8 R10 R20 O1 O2 O8 Hw64 Ha Ha16 Hk Hn Hki Hkn
  Hcap Hs4 Hsc Hs8 Dso SIMG SWR ORA SRA OSH SSH WS WO).
intros regsC memC mat D1 D2 D10 D11 D12 D9 Dkeep Dfr Dmem Dgrow Vs Vkids Vkeys Vn Vcap HJ5 HARU5.
rewrite Forall_forall in Hkeep, Dkeep.
assert (Hsp5 : spZ regsC = spZ regs - 48) by lia.
assert (E3 : YK11.getr regsC 3 = w64 (as_gp B))
  by (rewrite (Dkeep 3%bv ltac:(cbn; tauto)), (Hkeep 3%bv ltac:(cbn; tauto)); exact R3).
assert (E4 : YK11.getr regsC 4 = w64 (as_tp B))
  by (rewrite (Dkeep 4%bv ltac:(cbn; tauto)), (Hkeep 4%bv ltac:(cbn; tauto)); exact R4).
assert (Fr5 : pj_set_frame (mrestrict (w_H W4) memC) (spZ regs) regs).
{ replace (spZ regs) with (spZ regs4 + 48) by lia. exact Dfr. }
(* val is a pobj on stage D's memory: the slot and obj's fields are apart from it and off the shadow *)
assert (HPw5 : pobj tfibsegs B ly4 S4 W4 memC w).
{ apply (pSt_pobj_frame ly4 S4 W4 (unpoison U4 mem4) md4 mem4 memC w
    (fun x => slot <= x < slot + 8 \/ o + 24 <= x < o + 56) HAR4 HPw).
  - intros x Hx Hp. apply Dmem; [exact Hx | intros Hy; apply Hp; left; exact Hy | intros Hy; apply Hp; right; exact Hy].
  - intros x Hx [Hy|Hy]; lia.
  - intros x [Hy|Hy]; [apply SSH | apply OSH]; lia. }
(* ---- __asan_memcpy (kids + 56 n, val, 56), resuming at 0x83940 ---- *)
apply (pS_memcpy_call B HSS RT_memcpy ly S U W mem md ly4 S4 U4 W4 memC (with_vm_backing (m_vm_lazy md4) mat md4) FP
  (spZ regs) k4 regs regsC cnt fail live peak 6 kids keys n cap dst w _ HJ5 HARU5 FH Hsp5 eq_refl D1 D10 D11 D12 E3 E4
  HDB HPw5 Ddw WD Fr5).
intros regs6 mem6 md6 HJ6 HARU6 HP6 HS6 Hcp6 Hfr6 Hpr6.
assert (Hsp6 : spZ regs6 = spZ regs - 48).
{ unfold spZ. rewrite (fsw_pres regsC regs6 2%bv HP6 ltac:(unfold acallee_saved; vm_compute; lia)). exact Hsp5. }
(* val is a pobj after the memcpy: the destination is apart from it, the callee's window above alloc_ceiling *)
assert (HPw6 : pobj tfibsegs B ly4 S4 W4 mem6 w)
  by exact (pSt_pobj_rt ly4 S4 U4 W4 memC (with_vm_backing (m_vm_lazy md4) mat md4) mem6 w dst
              (spZ regs - 48 - ESTACK) (spZ regs - 48) HARU5 HPw5 Hfr6 Hpr6 DSH Hwin).
(* ---- STAGE E: 0x83940 .. jal __asan_memset (val, 0, 56) ---- *)
apply (pj_set_stageE B ly S W (unpoison U mem) md [] ly4 S4 U4 W4 regs regs6 mem6 md6 STK_pj_set (spZ regs) FP k4
  cnt fail live peak 6 kids keys n cap _ I HS6 HJ6 HARU6 Hsp6 S48).
intros regsE memE matE (E1 & E2 & Ekeep & Efr) (E10 & E11 & E12) SBE HJ7 HARU7.
rewrite Forall_forall in Ekeep.
assert (HspE : spZ regsE = spZ regs - 48) by lia.
assert (E3' : YK11.getr regsE 3 = w64 (as_gp B)).
{ rewrite (Ekeep 3%bv ltac:(cbn; tauto)), (fsw_pres regsC regs6 3%bv HP6 ltac:(unfold acallee_saved; vm_compute; lia)).
  exact E3. }
assert (E4' : YK11.getr regsE 4 = w64 (as_tp B)).
{ rewrite (Ekeep 4%bv ltac:(cbn; tauto)), (fsw_pres regsC regs6 4%bv HP6 ltac:(unfold acallee_saved; vm_compute; lia)).
  exact E4. }
assert (E10' : YK11.getr regsE 10 = w64 w).
{ rewrite E10, (fsw_pres regsC regs6 8%bv HP6 ltac:(unfold acallee_saved; vm_compute; lia)),
    (Dkeep 8%bv ltac:(cbn; tauto)). exact R8. }
assert (FrE : pj_set_frame (mrestrict (w_H W4) memE) (spZ regs) regs).
{ replace (spZ regs) with (spZ regs6 + 48) by lia. exact Efr. }
assert (HPw7 : pobj tfibsegs B ly4 S4 W4 memE w)
  by exact (pobj_below B ly4 S4 W4 (unpoison U4 mem6) md6 mem6 memE w
              (ARU_AR tfibsegs B ly4 S4 U4 W4 mem6 md6 HARU6) SBE HPw6).
(* ---- __asan_memset (val, 0, 56), resuming at 0x83950 ---- *)
apply (pS_memset_call B HSS RT_memset ly S U W mem md ly4 S4 U4 W4 memE (with_vm_backing (m_vm_lazy md6) matE md6) FP
  (spZ regs) k4 regs regsE cnt fail live peak 6 kids keys n cap w _ HJ7 HARU7 FH HspE eq_refl E1 E10' E11 E12 E3' E4'
  HPw7 WW FrE).
intros regs8 mem8 md8 HJ8 HARU8 HP8 HS8 Hz8 Hfr8 Hpr8.
assert (Hsp8 : spZ regs8 = spZ regs - 48).
{ unfold spZ. rewrite (fsw_pres regsE regs8 2%bv HP8 ltac:(unfold acallee_saved; vm_compute; lia)). exact HspE. }
assert (Hkeep8 : Forall (fun r => YK11.getr regs8 r = YK11.getr regs r) [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv).
{ apply Forall_forall. intros r Hr. pose proof (pSt_cs r Hr) as Hc.
  assert (HrE : In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv) by (cbn [In] in Hr |- *; tauto).
  assert (HrD : In r [3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv) by (cbn [In] in Hr |- *; tauto).
  rewrite (fsw_pres regsE regs8 r HP8 Hc), (Ekeep r HrE), (fsw_pres regsC regs6 r HP6 Hc), (Dkeep r HrD).
  exact (Hkeep r Hr). }
(* ---- STAGE F: 0x83950 .. the ret, a0 = 0 ---- *)
apply (pj_set_stageF B ly S W (unpoison U mem) md [] ly4 S4 U4 W4 regs regs8 mem8 md8 STK_pj_set (spZ regs) FP k4
  cnt fail live peak 6 kids keys n cap _ HS8 HJ8 HARU8 Hsp8 eq_refl S48 Hkeep8).
intros E' ssf msf matF HSf Hrv Hpc RF1 RF10 HPF SBF HJF HARUF.
assert (Hjalr : v_jalr (YK11.getr (ms_regs msf) 1) 0 = YK11.getr regs 1) by (rewrite RF1; exact Hra).
apply (fsw_retU B pj_set_tbl pj_set_tbl_ok W4 E' ssf msf (with_vm_backing (m_vm_lazy md8) matF md8) STK_pj_set
  (spZ regs) FP regs ly S U W mem md ly4 S4 U4 k4 Qf HSf Hrv Hpc Hjalr HJF HARUF HPF).
intros matQ.
refine (KQ memC mem6 memE mem8 (ms_regs msf) (ms_mem msf) _ Vs Vkids Vkeys Vn Vcap Dmem Hcp6 _ SBE Hz8 _ SBF RF10).
- intros x Hx Hnd. apply Hfr6; [lia | exact Hnd | lia].
- intros x Hx Hnw. apply Hfr8; [lia | exact Hnw | lia].
Qed.
End TL.
