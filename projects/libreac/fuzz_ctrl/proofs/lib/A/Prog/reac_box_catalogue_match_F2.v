(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths, module names and addresses changed; 1148 of its 1189 lines of code are new or changed and 207 lines of the source are left out. *)
(* Stretch S2 of the footprint (_F) re-run of reac_box_catalogue_match.v (source commit d69f7c708f6, proved on FACTS
   ed6b6b7b0ab) by the same script over lib/Lib/StepF; image fuzz_ctrl v1.9.0 asan, ELF fuzz_ctrl.debug sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd; route (a) of 22:20Z; for the cgif-form walk
   C_reac_box_catalogue_match.v only.

   S2 is the silent stretch from the return of `jal __asan_stack_malloc_2` (0x84508) to the `jal reac_ctrl_parse`
   (0x84684, state at the jal, before it executes), and the early-miss stretch 0x84720 -> the exit cut 0x84724.
   The walk takes only the side-stack arm (s2 = the fake frame, nonzero), so the real-stack arm 0x84510 /
   0x8451c-0x84534 is not re-run: cm_resume_F takes the fake-frame arm of __asan_stack_malloc_2's post as premises.
   The source runs it as part of cm_entry (after its evt_cut on the allocator contract), cm_header, cm_gate and the
   first step of cm_miss_holds; each is re-stepped here as an ExecF.evtF under a universally quantified footprint
   RNG, with one rng premise per region the run reads or writes (instruction fetch is not an access), and with the
   continuation Q of the source replaced by the post predicate of the stretch end (cmKBP / cmPBP / cmMissP / cmXCP),
   which is what the kit bridge lifts. The <r>_of_F corollaries re-derive the source's own evt statements with
   ExecF.rng_all. reac_box_catalogue_match.v is unchanged apart from comment text. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBox RcBoxLib RcSynth RcParse
  RcMatch RcMatchLib RcAsan RcAsanLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_box_model_block_c reac_box_model_block
  reac_box_catalogue_match_c reac_box_catalogue_match_lib reac_box_catalogue_match.
(* Route (C): the narrowed premise and the `_on` run (Required, not Imported: its Section names are re-used below at
   Section MatchFOn's variables). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_match_on.
(* Last: StepF's step / store_done (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
(* The store hook the scripts below use (StepF's store_done calls it): also transport rd_mono across a store. Text of
   lib/A/Prog/MemMono.v (at head lib/A/Prog/MemMono.v:207-217; from a working branch 8bac67328ab), Local here. *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* The source file's names (its `Section Match` is closed, so each is applied below to this section's variables). *)
Module CM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_match.
Module CMO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_match_on.

(* ---------------------------------------------------------------------------------------------------------- *)
(* Route (C) (frozen form, a Theorem Labs lane 10:49Z): the `_on` forms of this file's SR-dependent declarations. Section
   MatchFOn has Section MatchF's binders and premises with `SR : shadow_rw m` narrowed to
   `SR_on : shadow_rw_on R m` (R = reac_box_catalogue_match_shadow_R f len S FS, a Theorem Labs lane's,
   reac_box_catalogue_match_c.v). The invariant and the continuations are reac_box_catalogue_match_on.v's (cmInv_on,
   cmKB_on, cmPB_on, cmMiss_on, cmPost_on); the post predicates are the old ones over cmInv_on (cmKBP_on, cmPBP_on,
   cmMissP_on, cmXCP_on, cmGP_on); each script is the old one with the names reac_box_catalogue_match_on.v re-proves
   (fk_facts_on, cm_inv_step_on, cm_mk_inv_on, cm_exit_on). The old statements of Section MatchF are corollaries of
   these, by the three conversions cmInv_on_of_cmInv, cmInv_of_on and cmPost_of_on. cm_miss_F keeps its own
   (four-step) script: its generalized form takes no premise, so a corollary through cmInv_of_on (which needs SR)
   would add SR to it. *)
Section MatchFOn.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis RS : S < 2^64.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HK : 9136 <= S.
Hypothesis ST : stk rsegs m (S - 9136) S.
Hypothesis Hwin : forall a, S - 9136 <= a < S -> seg_rom rsegs (wa a) = None.
Hypothesis Hfb : length fb = 50%nat.
Hypothesis HF : 50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fb /\ (f + 50 <= S - 9136 \/ S <= f).
Hypothesis HT : forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a).
Hypothesis MI : mem_inv rsegs m.
Hypothesis AC : asan_cells m.
Hypothesis SR_on : shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) m.
Hypothesis HHM : HIGHMEM_BEG <= S - 9136.
Hypothesis HAE : S <= APPMEM_END.
Hypothesis AW : addressable m (S - 9136) 9136.
Hypothesis AFU : 50 <= len -> addressable m f 50 /\ app_mem (f + 50).
Hypothesis AT : addressable m CM_T 3256.
Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
Hypothesis HGOT : bytes_at rsegs m GOT_CF (le8 (wa CF)).
Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Hypothesis FP0 : fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - 9136) S
  (reac_box_catalogue_match_W S) (reac_box_catalogue_match_D f len).
Hypothesis TLS0 : reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - 9136) S.

(* The names of reac_box_catalogue_match.v (old, re-used) and of reac_box_catalogue_match_on.v (re-proved), at this
   section's variables and hypotheses (on-api.md prefixes, SR_on in place of SR). *)
Local Abbreviation CA := (CM.CA S).
Local Abbreviation cmFK := (CM.cmFK S FS).
Local Abbreviation cmSAVES := (CM.cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).
Local Abbreviation cmHF := (CM.cmHF S).
Local Abbreviation aWc := (CM.aWc S FS).
Local Abbreviation aXs := (CM.aXs S FS).
Local Abbreviation cmInv := (CM.cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Abbreviation cmPost := (CM.cmPost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Local Abbreviation cmInv_on := (CMO.cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Abbreviation cmKB_on := (CMO.cmKB_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS).
Local Abbreviation cmPB_on := (CMO.cmPB_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Local Abbreviation cmMiss_on := (CMO.cmMiss_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Local Abbreviation cmPost_on := (CMO.cmPost_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Local Abbreviation acl_fs := (CM.acl_fs tp m f len S FS FP0).
Local Abbreviation CA_facts := (CM.CA_facts f len S fb Rf Rlen S16 Hfb).
Local Abbreviation cm_CA_lo := (CM.cm_CA_lo f len S fb Rf Rlen S16 Hfb).
Local Abbreviation cm_sh_add8 := (CM.cm_sh_add8 f len S fb Rf Rlen Hfb).
Local Abbreviation fk_facts_on := (CMO.fk_facts_on tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR_on AW FP0).
Local Abbreviation cm_fr_bounds := (CM.cm_fr_bounds tp m f len S FS fb Rf Rlen S16 HK Hfb HHM FP0).
Local Abbreviation cm_inv_step_on :=
  (CMO.cm_inv_step_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb Rf Rlen S16 HK ST Hfb SR_on HHM HAE AW
     FP0).
Local Abbreviation cm_mk_inv_on :=
  (CMO.cm_mk_inv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb Rf Rlen S16 HK ST Hfb AC SR_on HHM HAE AW
     FP0 TLS0).
Local Abbreviation cm_exit_on :=
  (CMO.cm_exit_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb Rf Rlen RS S16 HK ST Hfb SR_on
     HHM HAE AW FP0).
Local Abbreviation cm_flag_upd := (CM.cm_flag_upd f len S FS fb Rf Rlen HK Hfb).
Local Abbreviation cm_FB := (CM.cm_FB tp m f len S FS fb Rf Rlen HK Hfb HF HAE AFU FP0).
Local Abbreviation cm_AF := (CM.cm_AF tp m f len S FS fb Rf Rlen S16 HK Hfb HF HHM HAE AFU FP0).
Local Abbreviation cm_parse_addr := (CM.cm_parse_addr f len S fb Rf Rlen Hfb).
Local Abbreviation cm_miss_short := (CM.cm_miss_short len fb).
Local Abbreviation cm_miss_hdr := (CM.cm_miss_hdr len fb).
Local Abbreviation sh_out_app := (CM.sh_out_app f len S fb Rf Rlen Hfb).

(* The conversions the old statements' corollaries use (on-api.md): the invariant narrowed and back (the shadow
   conjunct: shadow_rw_on_of_shadow_rw; shadow_rw_mono from the invariant's wmono m mc / rd_mono m mc), and the exit
   post (shadow_rw of the post memory from its post form at the whole shadow). *)
Lemma cmInv_on_of_cmInv : forall fr sp2 jj nn mc, cmInv fr sp2 jj nn mc -> cmInv_on fr sp2 jj nn mc.
Proof.
  intros fr sp2 jj nn mc (FK & MU & WM & RM & MIc & ACc & SRc & R).
  exact (conj FK (conj MU (conj WM (conj RM (conj MIc (conj ACc (conj (shadow_rw_on_of_shadow_rw _ mc SRc) R))))))).
Qed.

Lemma cmInv_of_on : shadow_rw m -> forall fr sp2 jj nn mc, cmInv_on fr sp2 jj nn mc -> cmInv fr sp2 jj nn mc.
Proof.
  intros SR0 fr sp2 jj nn mc (FK & MU & WM & RM & MIc & ACc & _ & R).
  exact (conj FK (conj MU (conj WM (conj RM (conj MIc (conj ACc (conj (shadow_rw_mono m mc SR0 WM RM) R))))))).
Qed.

Lemma cmPost_of_on : shadow_rw m -> forall ms', cmPost_on ms' -> cmPost ms'.
Proof.
  intros SR0 ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & ST' & AC' & SH & AD & FP' & TL').
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  refine (conj E (conj MU (conj WM (conj MI' (conj ST' (conj AC' (conj _ (conj AD (conj FP' TL'))))))))).
  exact (shadow_rw_of_on_all m' (SH _ (shadow_rw_on_of_shadow_rw _ m SR0))).
Qed.

(* The post predicates of the stretch ends over cmInv_on (the old ones, cmInv narrowed). *)
Definition cmKBP_on (fr sp2 jj nn : Z) : machine_state -> Prop := fun ms =>
  exists (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    ms = MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
                 ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
                 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
            F (Z_to_bv 64 0x845dc) fc None mc (seg_rom rsegs)
    /\ cmInv_on fr sp2 jj nn mc.

Definition cmPBP_on (fr sp2 jj nn : Z) : machine_state -> Prop := fun ms =>
  exists (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    ms = MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
                 (Z_to_bv 64 f) (Z_to_bv 64 len) (Z_to_bv 64 (fr + 32)) ra3 ra4 ra5 ra6 ra7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
                 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
            F (Z_to_bv 64 0x84684) fc None mc (seg_rom rsegs)
    /\ 50 <= len /\ cp_v fb 12 = 0x88 /\ cp_v fb 13 = 0x19 /\ cp_v fb 16 = 0xcd /\ cp_v fb 17 = 0xea
    /\ cmInv_on fr sp2 jj nn mc /\ addressable mc (fr + 32) 36.

Definition cmMissP_on (fr sp2 jj nn : Z) : machine_state -> Prop := fun ms =>
  exists (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    ms = MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
                 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
                 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
            F (Z_to_bv 64 0x84720) fc None mc (seg_rom rsegs)
    /\ want CM_T len fb = 0 /\ cmInv_on fr sp2 jj nn mc.

Definition cmXCP_on (fr sp2 jj nn : Z) : machine_state -> Prop := fun ms =>
  exists (r : Z) (mc : word -> option byte)
         (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
    ms = MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
                 (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x84724) fc None mc (seg_rom rsegs)
    /\ r = want CM_T len fb /\ cmInv_on fr sp2 jj nn mc.

Definition cmGP_on (fr sp2 jj nn : Z) : machine_state -> Prop :=
  fun ms => cmPBP_on fr sp2 jj nn ms \/ cmMissP_on fr sp2 jj nn ms.

(* Section MatchF's file-local tactics, the same text (a section's Ltac ends with it). *)
Ltac steps_until_if :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

Ltac chk_core X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evtF ?segs ?RNG0 ?Q (MS ?R ?F0 (if _ then _ else ?B) ?fc0 ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RNG0 Q (MS (bvmap_set r rr R) F0 B fc0 rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_land7; extra X;
          step;
          let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
          first [ rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 1) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 1 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 3) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 3 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]) ];
          clear MB; bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac pre_sr X RX := step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_shr3.
Ltac no_extra X := idtac.

Ltac cm_hdr_out HFSapp HHm8 :=
  cbn [outside]; unfold fs_hint, fs_flag, fs_M in *; cbn [Z.of_nat] in *;
  repeat first [ change (2 ^ 15) with 32768 in *
               | change (2 ^ (15 - 0)) with 32768 in *
               | change (2 ^ (14 - 0)) with 16384 in *
               | change (2 ^ (15 - 1)) with 16384 in *
               | change (2 ^ (14 - 1)) with 8192 in *
               | change (2 ^ (15 - 2)) with 8192 in * ];
  repeat split; try exact I;
  first
    [ lia
    | match goal with
      | |- ~ (shadow_addr ?frr <= ?xx < _) =>
          let A := fresh "A" in let B := fresh "B" in intros [A B];
          pose proof (acl_sh_out xx frr (frr + 8 * 32) ltac:(apply HFSapp; unfold FS_SIZE; lia)
                        ltac:(lia) ltac:(unfold APPMEM_END; lia)) as Hso;
          rewrite (cm_sh_add8 frr 32 HHm8) in Hso; apply Hso; split; [exact A | exact B]
      end ].

Ltac cm_wv :=
  let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  match goal with
  | |- wview _ _ (wa ?x) <> None =>
    first
      [ match goal with H : forall a, _ -> wview rsegs m (wa a) <> None |- _ => apply H; lia end
      | match goal with H : forall k, 0 <= k < 192 -> wview rsegs m (wa (?fr + k)) <> None |- _ =>
          replace x with (fr + (x - fr)) by lia; apply H; lia end
      | match goal with H : forall k, 0 <= k < 24 -> wview rsegs m (wa (?s + k)) <> None |- _ =>
          replace x with (s + (x - s)) by lia; apply H; lia end ]
  end.

Ltac cm_wst a n :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa a) n = true)
        by (eapply wv_store_ok;
            [ cm_wv | eassumption
            | try unfold shadow_addr; try unfold ASAN_K; Z.div_mod_to_equations; lia
            | try unfold shadow_addr; try unfold ASAN_K; Z.div_mod_to_equations; lia ])
  end.

Ltac cm_keep HB :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F0 ?pc ?fc0 ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
      let E := addr_expr a in
      change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs);
      assert (HB : bytes_at segs (write_to_mem mm (wa E) bs) E bs)
        by (apply bytes_at_write_same; first [simpl_sizes | cbn [length]]; lia);
      store_done
  end.

(* (1) cm_header_F at cmInv_on / cmKBP_on (fk_facts_on, cm_inv_step_on). *)
Lemma cm_header_F_on : forall (RNG : footprint) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rt3 rt4 rt5 rt6 : word),
  rng RNG (CA + 24) 8 -> rng RNG fr 24 -> rng RNG (fr / 8 + ASAN_K) 24 ->
  cmInv_on fr sp2 jj nn mc ->
  evtF rsegs RNG (cmKBP_on fr sp2 jj nn)
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             rs6 (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x84538) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rt3 rt4 rt5 rt6
    RCA RFR RSH INV.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  clear MUg.
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & FSPc).
  assert (cmSTW : forall a, S - 9136 <= a < S -> wview rsegs m (wa a) <> None)
    by (intros a Ha; exact (stk_wv m _ _ _ ST Ha)).
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  assert (RMh : rd_mono mc mc) by apply rd_mono_refl.
  unfold cmHF, shadow_addr in MUh.
  cm_wst (CA + 24) 8%nat. step. store_done.
  do 3 step.
  step. rewrite (unsigned_lit fr) by lia. rewrite rc_shr3.
  do 6 step.
  cm_wst fr 8%nat. step. store_done.
  cm_wst (fr + 8) 8%nat. step. store_done.
  cm_wst (fr + 16) 8%nat. step. store_done.
  step. step.
  assert (SHlo : 0 <= fr / 8 + ASAN_K).
  { assert (0 <= fr / 8) by (apply Z.div_pos; lia). unfold ASAN_K; lia. }
  assert (SHhi : fr / 8 + ASAN_K + 24 <= 2 ^ 64).
  { unfold ASAN_K. Z.div_mod_to_equations. lia. }
  cm_wst (fr / 8 + ASAN_K) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 1) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 2) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 3) 1%nat. step. store_done.
  step.
  cm_wst (fr / 8 + ASAN_K + 4) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 5) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 6) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 7) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 8) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 9) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 10) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 11) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 12) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 13) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 14) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 15) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 20) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 21) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 22) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 23) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 16) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 17) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 18) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 19) 1%nat. step. store_done.
  apply evtF_done. unfold cmKBP_on.
  eexists. do 15 eexists. split; [reflexivity|].
  eapply cm_inv_step_on; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
Qed.

(* (2a) cm_resume_rb_F at cmInv_on / cmKBP_on (cm_header_F_on). *)
Lemma cm_resume_rb_F_on : forall (RNG : footprint) (jj : Z)
    (rr u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
  0 <= jj < fs_M 2 ->
  rng RNG (CA + 24) 8 -> rng RNG (fs_frame FS 2 jj) 24 -> rng RNG (fs_frame FS 2 jj / 8 + ASAN_K) 24 ->
  cmInv_on (fs_frame FS 2 jj) CA jj 1 m ->
  evtF rsegs RNG (cmKBP_on (fs_frame FS 2 jj) CA jj 1)
    (MS (mkR rr (Z_to_bv 64 CA) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             (Z_to_bv 64 (fs_frame FS 2 jj)) x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84508) fc None m (seg_rom rsegs)).
Proof.
  intros RNG jj rr u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 Hjj RCA RFR RSH INV.
  pose proof INV as INVk.
  pose proof INV as INVf. destruct INVf as (FK & _).
  pose proof (cm_fr_bounds (fs_frame FS 2 jj) CA jj 1 FK) as (FRgt & FRhi). unfold ASAN_GT in FRgt.
  pose proof RS as RS'.
  step. step. step. step.
  rewrite (rc_neq0_64 (fs_frame FS 2 jj)) by lia. cbn [negb]. cbv iota.
  eapply (cm_header_F_on RNG (fs_frame FS 2 jj) CA jj 1 m); [exact RCA | exact RFR | exact RSH | exact INVk].
Qed.

(* (2) cm_resume_F at cmKBP_on (cm_header_F_on, cm_mk_inv_on). *)
Lemma cm_resume_F_on : forall (RNG : footprint) (m0 m2 : word -> option byte) (h h2 a0 : word)
    (flags : list byte) (ii : Z) (u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
  rng RNG (CA + 24) 8 ->
  rng RNG (fs_frame FS 2 ((bv_unsigned h + ii) mod fs_M 2)) 24 ->
  rng RNG (fs_frame FS 2 ((bv_unsigned h + ii) mod fs_M 2) / 8 + ASAN_K) 24 ->
  munch [(S - 9136, S)] m m0 -> wmono rsegs m m0 -> rd_mono m m0 ->
  rw_cells rsegs m0 (S - 96) cmSAVES ->
  bytes_at rsegs m0 (fs_hint FS 2) (le8 h) ->
  bytes_at rsegs m0 (fs_flag FS 2 0) flags -> Z.of_nat (length flags) = fs_M 2 ->
  Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags ->
  wmono rsegs m0 m2 -> mem_inv rsegs m2 -> stk rsegs m2 (S - 9136) CA -> fs_place m2 FS ->
  bytes_at rsegs m2 (fs_hint FS 2) (le8 h2) ->
  0 <= ii < fs_M 2 ->
  (forall i', 0 <= i' < ii -> nth_error flags (Z.to_nat ((bv_unsigned h + i') mod fs_M 2)) = Some (Z_to_bv 8 1)) ->
  nth_error flags (Z.to_nat ((bv_unsigned h + ii) mod fs_M 2)) = Some (Z_to_bv 8 0) ->
  asan_stack_malloc_frame 2 ASAN_STACK_MALLOC_K (Z_to_bv 64 CA) 192 FS
    ((bv_unsigned h + ii) mod fs_M 2) a0 m0 m2 ->
  evtF rsegs RNG (cmKBP_on (fs_frame FS 2 ((bv_unsigned h + ii) mod fs_M 2)) CA
                           ((bv_unsigned h + ii) mod fs_M 2) 1)
    (MS (mkR (Z_to_bv 64 0x84508) (Z_to_bv 64 CA) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             a0 x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K) s6 s7 s8 s9 s10 s11
             u3 u4 u5 u6)
         F (Z_to_bv 64 0x84508) fc None m2 (seg_rom rsegs)).
Proof.
  intros RNG m0 m2 h h2 a0 flags ii u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6
    RCA RFR RSH MU WM RM FR HH2 HF2 HFl2 HFb2 WM2 MI2 ST2 FSP2 HH2' Hii0 Hiipre Hiinth FRM.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
  step. step. step. step.
  pose proof acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  unfold ASAN_GT in FSgt. unfold FS_SIZE in FShi.
  pose proof FP0 as (DTx & TSx & Cx & Tx & DBx & kkx & _ & _ & _ & _ & _ & HCLx & _).
  pose proof HCLx as HCLy.
  apply Forall_cons_iff in HCLy as [(_ & h0 & flags0 & HH0 & HF0 & HFl0 & HFb0) HCLy1].
  apply Forall_cons_iff in HCLy1 as [(_ & h1 & flags1 & HH1 & HF1 & HFl1 & HFb1) HCLy2].
  apply Forall_cons_iff in HCLy2 as [(_ & h2m & flags2m & HH2m & HF2m & HFl2m & HFb2m) _].
  unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
  rewrite (unsigned_lit CA) in FRM by lia.
  replace (fs_B 2) with 256 in FRM by reflexivity.
  replace (fs_shadow_n 2 192) with 32 in FRM by reflexivity.
  destruct FRM as (Ex0 & Hm64 & _ & HFL & H24 & Hflagword & HSH & HADD & STF & APF & FSlo & FShi' & GT & FRA' & DIS & MU2).
  remember ((bv_unsigned h + ii) mod fs_M 2) as jj eqn:Ejj.
  assert (Hjj : 0 <= jj < fs_M 2) by (subst jj; apply Z.mod_pos_bound; reflexivity).
  remember (fs_frame FS 2 jj) as fr eqn:Efr.
  subst a0.
  unfold FS_SIZE in FShi'. change (fs_M 2) with 4096 in Hjj.
  replace (fr + 256 - 8) with (fr + 248) in * by lia.
  assert (Hm8 : fr mod 8 = 0) by (clear -Hm64; Z.div_mod_to_equations; lia).
  unfold ASAN_STACK_MALLOC_K in MU2.
  assert (RFRf : rng RNG fr 24) by (subst fr; subst jj; exact RFR).
  assert (RSHf : rng RNG (fr / 8 + ASAN_K) 24) by (subst fr; subst jj; exact RSH).
  unfold ASAN_GT in GT.
  assert (Hfrlo : FS + 36864 <= fr) by
    (rewrite Efr; unfold fs_frame, fs_B; cbn [Z.of_nat]; change (2 ^ 20) with 1048576; change (2 ^ 2) with 4; lia).
  rewrite (rc_neq0_64 fr) by lia. cbn [negb]. cbv iota.
  assert (RM2r : rd_mono m0 m2).
  { apply (rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
    - apply (rd_of_bytes _ _ _ HH2'). rewrite length_le8. cbn [Z.of_nat]. unfold fs_hint in *. lia.
    - apply (rd_of_bytes _ _ _ HFL). cbn [length]. lia.
    - apply (rd_of_bytes _ _ _ H24). rewrite length_le8. cbn [Z.of_nat]. lia.
    - apply (rd_of_bytes _ _ _ Hflagword). rewrite length_le8. cbn [Z.of_nat]. lia.
    - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
    - apply (rd_of_stk _ _ _ ST2). lia. }
  assert (RMw : rd_mono m m2) by (apply (rd_mono_trans _ _ _ RM RM2r)).
  assert (WMw : wmono rsegs m m2) by (apply (wmono_trans _ _ _ _ WM WM2)).
  assert (FR2 : rw_cells rsegs m2 (S - 96) cmSAVES).
  { apply (rw_cells_transport rsegs _ m0 m2 _ _ FR MU2 WM2).
    cbn [disjoint_from cells_size csize Nat.add cmSAVES].
    unfold fs_hint, fs_flag, fs_M. cbn [Z.of_nat]. change (2 ^ 15) with 32768. change (2 ^ (15 - 2)) with 8192.
    repeat split; right; first [ lia | (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia) ]. }
  assert (MUw : munch [(S - 9136, S); (fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1);
                       (fr + 24, fr + 32); (fr + 248, fr + 256); (shadow_addr fr, shadow_addr fr + 32); (CA - 208, CA)] m m2).
  { apply (munch_trans _ m m0 m2).
    - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *.
      split; [exact (proj1 Hx) | exact I].
    - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in Hx. exact (proj2 Hx). }
  eapply (cm_header_F_on RNG fr CA jj 1 m2); [ exact RCA | exact RFRf | exact RSHf |].
  apply (cm_mk_inv_on fr CA jj 1 m2 [(S - 9136, S); (fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1);
                   (fr + 24, fr + 32); (fr + 248, fr + 256); (shadow_addr fr, shadow_addr fr + 32); (CA - 208, CA)]).
  + right. split; [exact Hjj | split; [exact Efr | split; reflexivity]].
  + exact MUw.
  + exact WMw.
  + exact RMw.
  + exact MI2.
  + intros x Hx. unfold aWc in Hx. cbn [outside] in Hx. destruct Hx as (Hwn & Hxs).
    unfold aXs in Hxs. apply cm_out_app in Hxs. destruct Hxs as (Hfpw & Hws).
    cbn [outside] in Hws. destruct Hws as (Hws & _).
    cbn [outside]. split; [exact Hwn|]. split.
    { exact (out_in _ _ _ _ Hfpw (fpw3_in_hint FS 2 ltac:(cbn; tauto))). }
    split.
    { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_flag FS 2 ltac:(cbn; tauto))).
      unfold fs_flag, fs_M in *. destruct Hc. split; lia. }
    split.
    { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))).
      rewrite Efr in *. unfold fs_frame, fs_B, fs_M in *. cbn [Z.of_nat] in *.
      change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in Hjj.
      destruct Hc. split; lia. }
    split.
    { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))).
      rewrite Efr in *. unfold fs_frame, fs_B, fs_M in *. cbn [Z.of_nat] in *.
      change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in Hjj.
      destruct Hc. split; lia. }
    split.
    { pose proof (out_in _ _ _ _ Hfpw (fpw3_in_shadow FS 2 ltac:(cbn; tauto))) as HFin.
      assert (GE : shadow_addr (fs_frame FS 2 0) <= shadow_addr fr).
      { apply acl_sh_ge. rewrite Efr. unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576. lia. }
      assert (LE : shadow_addr fr + 32 <= shadow_addr (fs_frame FS 2 (fs_M 2))).
      { rewrite Efr. unfold shadow_addr, fs_frame, fs_B, fs_M in *. cbn [Z.of_nat] in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ (14 - 2)) with 4096 in Hjj.
        Z.div_mod_to_equations; lia. }
      intros [A B]. clear -HFin GE LE A B. lia. }
    split; [|exact I].
    intros Hc. apply Hwn. clear -Hc CAlo2 CAhi2. lia.
  + intros y Hy Hap. pose proof (rt_app_shadow y Hap) as Hsh.
    cbn [outside]. split.
    { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh.
      clear -Hsh Hy HHM'. lia. }
    split.
    { apply (sh_out_app (shadow_addr y) (fs_hint FS 2) (fs_hint FS 2 + 8) Hsh).
      intros z Hz. apply FSapp. unfold fs_hint in *. unfold FS_SIZE. lia. }
    split.
    { apply (sh_out_app (shadow_addr y) (fs_flag FS 2 jj) (fs_flag FS 2 jj + 1) Hsh).
      intros z Hz. apply FSapp. unfold fs_flag, fs_M in *. cbn [Z.of_nat] in *.
      change (2 ^ 15) with 32768 in *. change (2 ^ (15 - 2)) with 8192 in *. unfold FS_SIZE. lia. }
    split.
    { apply (sh_out_app (shadow_addr y) (fr + 24) (fr + 32) Hsh).
      intros z Hz. apply APF. lia. }
    split.
    { apply (sh_out_app (shadow_addr y) (fr + 248) (fr + 256) Hsh).
      intros z Hz. apply APF. lia. }
    split; [|split; [|exact I]].
    { intros [A B]. pose proof (acl_sh_ge y (fr + 8 * 32) ltac:(lia)) as G.
      rewrite (cm_sh_add8 fr 32 Hm8) in G. lia. }
    { apply (sh_out_app (shadow_addr y) (CA - 208) CA Hsh).
      intros z Hz. right. unfold HIGHMEM_BEG, APPMEM_END. clear -Hz Hy HHM' HAE' CAlo2 CAhi2. lia. }
  + intros c Hc. cbn in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; subst c.
    * split.
      -- exists h0. apply (fl_bytes _ m _ (fs_hint FS 0) (le8 h0) HH0 MUw).
         intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
         cm_hdr_out FSapp Hm8.
      -- exists flags0. split; [|split; [exact HFl0 | exact HFb0]].
         apply (fl_bytes _ m _ (fs_flag FS 0 0) flags0 HF0 MUw).
         intros x Hx. rewrite HFl0 in Hx.
         cm_hdr_out FSapp Hm8.
    * split.
      -- exists h1. apply (fl_bytes _ m _ (fs_hint FS 1) (le8 h1) HH1 MUw).
         intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
         cm_hdr_out FSapp Hm8.
      -- exists flags1. split; [|split; [exact HFl1 | exact HFb1]].
         apply (fl_bytes _ m _ (fs_flag FS 1 0) flags1 HF1 MUw).
         intros x Hx. rewrite HFl1 in Hx.
         cm_hdr_out FSapp Hm8.
    * split.
      -- exists h2. exact HH2'.
      -- apply (cm_flag_upd m0 m2
           [(fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1);
            (fr + 24, fr + 32); (fr + 248, fr + 256); (shadow_addr fr, shadow_addr fr + 32); (CA - 208, CA)]
           flags jj Hjj HFl2 HFb2 HF2 MU2); [| exact HFL].
         intros x Hx Hxne.
         assert (Hxap : app_mem x) by (apply FSapp; unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
           change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; unfold FS_SIZE; lia).
         cbn [outside]. split.
         { unfold fs_hint, fs_flag, fs_M in *; cbn [Z.of_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; lia. }
         split.
         { intros [A B]. apply Hxne. unfold fs_flag in *. lia. }
         split.
         { unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; lia. }
         split.
         { unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; lia. }
         split; [|split; [|exact I]].
         { intros [A B]. pose proof (acl_sh_out x fr (fr + 8 * 32) Hxap ltac:(lia) ltac:(unfold APPMEM_END; lia)) as Hso.
           rewrite (cm_sh_add8 fr 32 Hm8) in Hso. apply Hso. split; [exact A | exact B]. }
         { unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; lia. }
  + exact FR2.
  + intros _. exact Hflagword.
Qed.

(* (3) cm_gate_F at cmInv_on / cmGP_on (fk_facts_on, cm_inv_step_on). *)
Lemma cm_gate_F_on : forall (RNG : footprint) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  (50 <= len -> rng RNG f 50) ->
  (50 <= len -> rng RNG (f / 8 + ASAN_K) ((f + 49) / 8 - f / 8 + 1)) ->
  rng RNG (fr / 8 + ASAN_K) 24 ->
  cmInv_on fr sp2 jj nn mc ->
  evtF rsegs RNG (cmGP_on fr sp2 jj nn)
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x845dc) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 RDAT RSHD RSH INV.
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & _).
  step.
  rewrite cm_ltu_lit by (clear -Rlen; lia).
  destruct (Z.ltb_spec len 50) as [L|L]; cbv iota.
  { apply evtF_done. unfold cmGP_on. right. unfold cmMissP_on.
    exists mc. do 16 eexists. split; [reflexivity|].
    split; [exact (cm_miss_short L) | exact INVk]. }
  pose proof (RDAT L) as RD50. pose proof (RSHD L) as RDSH.
  destruct (HF L) as (Hf0 & Hf50 & _ & _).
  pose proof (cm_FB mc L MUg) as BF.
  pose proof (cm_AF mc L MUg) as AF.
  clear MUg.
  pose proof (rd_byte rsegs mc f fb 12 BF ltac:(rewrite Hfb; clear; lia)) as R12.
  pose proof (rd_byte rsegs mc f fb 13 BF ltac:(rewrite Hfb; clear; lia)) as R13.
  pose proof (rd_byte rsegs mc f fb 16 BF ltac:(rewrite Hfb; clear; lia)) as R16.
  pose proof (rd_byte rsegs mc f fb 17 BF ltac:(rewrite Hfb; clear; lia)) as R17.
  change (Z.of_nat 12) with 12 in R12. change (Z.of_nat 13) with 13 in R13.
  change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 17) with 17 in R17.
  clear BF.
  assert (RSH12 : rng RNG ((f + 12) / 8 + ASAN_K) 1).
  { apply (rng_sub' RNG (f / 8 + ASAN_K) ((f + 49) / 8 - f / 8 + 1) _ _ RDSH).
    pose proof (Z.div_le_mono f (f + 12) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (f + 12) (f + 49) 8 ltac:(lia) ltac:(lia)). split; lia. }
  assert (RSH13 : rng RNG ((f + 13) / 8 + ASAN_K) 1).
  { apply (rng_sub' RNG (f / 8 + ASAN_K) ((f + 49) / 8 - f / 8 + 1) _ _ RDSH).
    pose proof (Z.div_le_mono f (f + 13) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (f + 13) (f + 49) 8 ltac:(lia) ltac:(lia)). split; lia. }
  assert (RSH16 : rng RNG ((f + 16) / 8 + ASAN_K) 1).
  { apply (rng_sub' RNG (f / 8 + ASAN_K) ((f + 49) / 8 - f / 8 + 1) _ _ RDSH).
    pose proof (Z.div_le_mono f (f + 16) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (f + 16) (f + 49) 8 ltac:(lia) ltac:(lia)). split; lia. }
  assert (RSH17 : rng RNG ((f + 17) / 8 + ASAN_K) 1).
  { apply (rng_sub' RNG (f / 8 + ASAN_K) ((f + 49) / 8 - f / 8 + 1) _ _ RDSH).
    pose proof (Z.div_le_mono f (f + 17) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (f + 17) (f + 49) 8 ltac:(lia) ltac:(lia)). split; lia. }
  clear RDSH.
  pose proof (byte_range (nth 12 fb (Z_to_bv 8 0))) as BR12. pose proof (byte_range (nth 13 fb (Z_to_bv 8 0))) as BR13.
  pose proof (byte_range (nth 16 fb (Z_to_bv 8 0))) as BR16. pose proof (byte_range (nth 17 fb (Z_to_bv 8 0))) as BR17.
  assert (RX12 : 0 <= f + 12 < 2^64) by (clear -Hf0 Hf50; lia).
  assert (RX13 : 0 <= f + 13 < 2^64) by (clear -Hf0 Hf50; lia).
  assert (RX16 : 0 <= f + 16 < 2^64) by (clear -Hf0 Hf50; lia).
  assert (RX17 : 0 <= f + 17 < 2^64) by (clear -Hf0 Hf50; lia).
  pose proof (acl_shadow mc f 50 12 1 (f + 12) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 12) 8 eq_refl); clear -H; lia) eq_refl) as SH12.
  pose proof (acl_shadow mc f 50 13 1 (f + 13) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 13) 8 eq_refl); clear -H; lia) eq_refl) as SH13.
  pose proof (acl_shadow mc f 50 16 1 (f + 16) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 16) 8 eq_refl); clear -H; lia) eq_refl) as SH16.
  pose proof (acl_shadow mc f 50 17 1 (f + 17) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 17) 8 eq_refl); clear -H; lia) eq_refl) as SH17.
  clear AF.
  (* byte 12: 0x88 *)
  step.
  chk_core (f + 12) RX12 (Z_to_bv 5 12) SH12 pre_sr no_extra.
  step. step. step.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 12 fb (Z_to_bv 8 0))) 136) as [E12|E12]; cbn [negb]; cbv iota.
  2: { apply evtF_done. unfold cmGP_on. right. unfold cmMissP_on.
       exists mc. do 16 eexists. split; [reflexivity|].
       split; [exact (cm_miss_hdr 12%nat 136 L ltac:(clear; lia) E12) | exact INVk]. }
  (* byte 13: 0x19 *)
  step.
  chk_core (f + 13) RX13 (Z_to_bv 5 12) SH13 pre_sr no_extra.
  step. step. step.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 13 fb (Z_to_bv 8 0))) 25) as [E13|E13]; cbn [negb]; cbv iota.
  2: { apply evtF_done. unfold cmGP_on. right. unfold cmMissP_on.
       exists mc. do 16 eexists. split; [reflexivity|].
       split; [exact (cm_miss_hdr 13%nat 25 L ltac:(clear; lia) E13) | exact INVk]. }
  (* byte 16: 0xcd *)
  step.
  chk_core (f + 16) RX16 (Z_to_bv 5 12) SH16 pre_sr no_extra.
  step. step. step.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 16 fb (Z_to_bv 8 0))) 205) as [E16|E16]; cbn [negb]; cbv iota.
  2: { apply evtF_done. unfold cmGP_on. right. unfold cmMissP_on.
       exists mc. do 16 eexists. split; [reflexivity|].
       split; [exact (cm_miss_hdr 16%nat 205 L ltac:(clear; lia) E16) | exact INVk]. }
  (* byte 17: 0xea *)
  step.
  chk_core (f + 17) RX17 (Z_to_bv 5 12) SH17 pre_sr no_extra.
  step. step. step.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 17 fb (Z_to_bv 8 0))) 234) as [E17|E17]; cbn [negb]; cbv iota.
  2: { apply evtF_done. unfold cmGP_on. right. unfold cmMissP_on.
       exists mc. do 16 eexists. split; [reflexivity|].
       split; [exact (cm_miss_hdr 17%nat 234 L ltac:(clear; lia) E17) | exact INVk]. }
  clear R12 R13 R16 R17 BR12 BR13 BR16 BR17 RX12 RX13 RX16 RX17.
  (* the un-poisoning of the parse buffer's shadow bytes 4..8 (all inside cmHF fr) *)
  step.
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & _ & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (_ & FRhi).
  assert (SHlo : 0 <= shadow_addr fr).
  { unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia). unfold ASAN_K. clear -D. lia. }
  assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64).
  { unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
  assert (FSW' : forall i, 0 <= i < 24 -> wview rsegs m (wa (shadow_addr fr + i)) <> None) by exact FSW.
  clear FSW.
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  assert (RMh : rd_mono mc mc) by apply rd_mono_refl.
  unfold cmHF in MUh.
  assert (RSHs : rng RNG (shadow_addr fr) 24) by (unfold shadow_addr; exact RSH).
  cm_wst (shadow_addr fr + 4) 1%nat. step. cm_keep B4.
  cm_wst (shadow_addr fr + 5) 1%nat. step. cm_keep B5.
  cm_wst (shadow_addr fr + 6) 1%nat. step. cm_keep B6.
  cm_wst (shadow_addr fr + 7) 1%nat. step. cm_keep B7.
  step.
  cm_wst (shadow_addr fr + 8) 1%nat. step. cm_keep B8.
  step. step.
  apply evtF_done. unfold cmGP_on. left. unfold cmPBP_on.
  do 14 eexists. split; [reflexivity|].
  split; [exact L|]. split; [exact E12|]. split; [exact E13|]. split; [exact E16|]. split; [exact E17|].
  split.
  - eapply cm_inv_step_on; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
  - eapply cm_parse_addr; [exact FR8 | clear -FRpos; lia | clear -FRhi HAE; lia | | exact B4 | exact B5 | exact B6
                          | exact B7 | exact B8].
    intros i Hi. replace (fr + 32 + i) with (fr + (32 + i)) by (clear; lia). apply FAP. clear -Hi; lia.
Qed.

(* (4) cm_miss_F at cmInv_on / cmXCP_on. *)
Lemma cm_miss_F_on : forall (RNG : footprint) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  want CM_T len fb = 0 -> cmInv_on fr sp2 jj nn mc ->
  evtF rsegs RNG (cmXCP_on fr sp2 jj nn)
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x84720) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 Hw INVk.
  step.
  apply evtF_done. unfold cmXCP_on.
  exists 0. exists mc. do 21 eexists. split; [reflexivity|].
  split; [symmetry; exact Hw | exact INVk].
Qed.

(* The old-Exec (evt) forms of the four runs at the `_on` continuations, from the footprint forms with rng_all. *)
Lemma cm_header_of_F_on : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rt3 rt4 rt5 rt6 : word),
  cmKB_on Q -> cmInv_on fr sp2 jj nn mc ->
  evt rsegs Q
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             rs6 (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x84538) fc None mc (seg_rom rsegs)).
Proof.
  intros Q fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rt3 rt4 rt5 rt6 K INV.
  pose proof INV as INVk. destruct INV as (FK & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi). unfold ASAN_GT in FRgt.
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof HK as HK'. pose proof RS as RS'.
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    eapply (cm_header_F_on RNG_all fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6
              rt3 rt4 rt5 rt6).
    - apply rng_all; lia.
    - apply rng_all; lia.
    - apply rng_all;
        [ assert (0 <= fr / 8) by (apply Z.div_pos; lia); unfold ASAN_K; lia
        | unfold ASAN_K; Z.div_mod_to_equations; lia ].
    - exact INVk. }
  intros ms' HP. unfold cmKBP_on in HP.
  destruct HP as (mc' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12
                  & w13 & w14 & w15 & E & INV'). subst ms'.
  eapply K. exact INV'.
Qed.

Lemma cm_resume_of_F_on : forall (m0 m2 : word -> option byte) (h h2 a0 : word)
    (flags : list byte) (ii : Z) (u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
  munch [(S - 9136, S)] m m0 -> wmono rsegs m m0 -> rd_mono m m0 ->
  rw_cells rsegs m0 (S - 96) cmSAVES ->
  bytes_at rsegs m0 (fs_hint FS 2) (le8 h) ->
  bytes_at rsegs m0 (fs_flag FS 2 0) flags -> Z.of_nat (length flags) = fs_M 2 ->
  Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags ->
  wmono rsegs m0 m2 -> mem_inv rsegs m2 -> stk rsegs m2 (S - 9136) CA -> fs_place m2 FS ->
  bytes_at rsegs m2 (fs_hint FS 2) (le8 h2) ->
  0 <= ii < fs_M 2 ->
  (forall i', 0 <= i' < ii -> nth_error flags (Z.to_nat ((bv_unsigned h + i') mod fs_M 2)) = Some (Z_to_bv 8 1)) ->
  nth_error flags (Z.to_nat ((bv_unsigned h + ii) mod fs_M 2)) = Some (Z_to_bv 8 0) ->
  asan_stack_malloc_frame 2 ASAN_STACK_MALLOC_K (Z_to_bv 64 CA) 192 FS
    ((bv_unsigned h + ii) mod fs_M 2) a0 m0 m2 ->
  evt rsegs (cmKBP_on (fs_frame FS 2 ((bv_unsigned h + ii) mod fs_M 2)) CA
                      ((bv_unsigned h + ii) mod fs_M 2) 1)
    (MS (mkR (Z_to_bv 64 0x84508) (Z_to_bv 64 CA) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             a0 x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K) s6 s7 s8 s9 s10 s11
             u3 u4 u5 u6)
         F (Z_to_bv 64 0x84508) fc None m2 (seg_rom rsegs)).
Proof.
  intros m0 m2 h h2 a0 flags ii u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6
    MU WM RM FR HH2 HF2 HFl2 HFb2 WM2 MI2 ST2 FSP2 HH2' Hii0 Hiipre Hiinth FRM.
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof HK as HK'. pose proof RS as RS'.
  pose proof FRM as FRMb. unfold asan_stack_malloc_frame in FRMb. cbv zeta in FRMb.
  rewrite (unsigned_lit CA) in FRMb by lia.
  destruct FRMb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GTb & FRAb & _).
  unfold ASAN_GT, ASAN_STACK_MALLOC_K in GTb, FRAb. replace (fs_B 2) with 256 in FRAb by reflexivity.
  apply (evtF_evt rsegs RNG_all).
  eapply (cm_resume_F_on RNG_all m0 m2 h h2 a0 flags ii u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6);
    try eassumption.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all;
      [ assert (0 <= fs_frame FS 2 ((bv_unsigned h + ii) mod fs_M 2) / 8) by (apply Z.div_pos; lia);
        unfold ASAN_K; lia
      | unfold ASAN_K; Z.div_mod_to_equations; lia ].
Qed.

Lemma cm_gate_of_F_on : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  cmPB_on Q -> cmMiss_on Q -> cmInv_on fr sp2 jj nn mc ->
  evt rsegs Q
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x845dc) fc None mc (seg_rom rsegs)).
Proof.
  intros Q fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 KP KM INV.
  pose proof INV as INVk. destruct INV as (FK & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi). unfold ASAN_GT in FRgt.
  pose proof RS as RS'.
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    eapply (cm_gate_F_on RNG_all fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6).
    - intros L. destruct (HF L) as (Hf0 & Hf50 & _ & _). apply rng_all; lia.
    - intros L. destruct (HF L) as (Hf0 & Hf50 & _ & _).
      apply rng_all;
        [ assert (0 <= f / 8) by (apply Z.div_pos; lia); unfold ASAN_K; lia
        | unfold ASAN_K; Z.div_mod_to_equations; lia ].
    - apply rng_all;
        [ assert (0 <= fr / 8) by (apply Z.div_pos; lia); unfold ASAN_K; lia
        | unfold ASAN_K; Z.div_mod_to_equations; lia ].
    - exact INVk. }
  intros ms' HP. unfold cmGP_on in HP. destruct HP as [HP|HP].
  - unfold cmPBP_on in HP.
    destruct HP as (mc' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12
                    & w13 & E & L & E12 & E13 & E16 & E17 & INV' & AD'). subst ms'.
    eapply KP; [exact L | exact E12 | exact E13 | exact E16 | exact E17 | exact INV' | exact AD'].
  - unfold cmMissP_on in HP.
    destruct HP as (mc' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12
                    & w13 & w14 & w15 & w16 & E & HW & INV'). subst ms'.
    eapply KM; [exact HW | exact INV'].
Qed.

Lemma cm_miss_of_F_on : cmMiss_on cmPost_on.
Proof.
  intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 Hw INVk.
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    eapply (cm_miss_F_on RNG_all fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6);
      [exact Hw | exact INVk]. }
  intros ms' HP. unfold cmXCP_on in HP.
  destruct HP as (r' & mc' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11
                  & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & E & Er & INV'). subst ms'.
  exact (cm_exit_on fr sp2 jj nn mc' r' w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20
           w21 Er INV').
Qed.

End MatchFOn.

Section MatchF.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis RS : S < 2^64.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HK : 9136 <= S.
Hypothesis ST : stk rsegs m (S - 9136) S.
Hypothesis Hwin : forall a, S - 9136 <= a < S -> seg_rom rsegs (wa a) = None.
Hypothesis Hfb : length fb = 50%nat.
Hypothesis HF : 50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fb /\ (f + 50 <= S - 9136 \/ S <= f).
Hypothesis HT : forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a).
Hypothesis MI : mem_inv rsegs m.
Hypothesis AC : asan_cells m.
Hypothesis SR : shadow_rw m.
Hypothesis HHM : HIGHMEM_BEG <= S - 9136.
Hypothesis HAE : S <= APPMEM_END.
Hypothesis AW : addressable m (S - 9136) 9136.
Hypothesis AFU : 50 <= len -> addressable m f 50 /\ app_mem (f + 50).
Hypothesis AT : addressable m CM_T 3256.
Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
Hypothesis HGOT : bytes_at rsegs m GOT_CF (le8 (wa CF)).
Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Hypothesis FP0 : fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - 9136) S
  (reac_box_catalogue_match_W S) (reac_box_catalogue_match_D f len).
Hypothesis TLS0 : reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - 9136) S.

(* The names of reac_box_catalogue_match.v's `Section Match`, applied to this section's variables and hypotheses
   (Coq discharges a section name over the section variables and hypotheses its statement or proof uses; the lists
   below are those Coq reports for the source's .vo). With them, every statement and script below is the source's
   text unchanged. *)

Local Notation CA := (CM.CA S).
Local Notation cmFK := (CM.cmFK S FS).
Local Notation cmSAVES := (CM.cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).
Local Notation cmHF := (CM.cmHF S).
Local Notation aWc := (CM.aWc S FS).
Local Notation aXs := (CM.aXs S FS).
Local Notation cmInv := (CM.cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Notation cmKB := (CM.cmKB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS).
Local Notation cmPB := (CM.cmPB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Local Notation cmMiss := (CM.cmMiss ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Local Notation cmPost := (CM.cmPost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Local Notation acl_fs := (CM.acl_fs tp m f len S FS FP0).
Local Notation CA_facts := (CM.CA_facts f len S fb Rf Rlen S16 Hfb).
Local Notation cm_CA_lo := (CM.cm_CA_lo f len S fb Rf Rlen S16 Hfb).
Local Notation cm_sh_add8 := (CM.cm_sh_add8 f len S fb Rf Rlen Hfb).
Local Notation fk_facts := (CM.fk_facts tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR AW FP0).
Local Notation cm_fr_bounds := (CM.cm_fr_bounds tp m f len S FS fb Rf Rlen S16 HK Hfb HHM FP0).
Local Notation cm_inv_step :=
  (CM.cm_inv_step ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb Rf Rlen S16 HK ST Hfb SR HHM HAE AW FP0).
Local Notation cm_mk_inv :=
  (CM.cm_mk_inv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb Rf Rlen S16 HK ST Hfb AC SR HHM HAE AW FP0
     TLS0).
Local Notation cm_header :=
  (CM.cm_header ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb Rf Rlen RS S16 HK ST Hfb SR
     HHM HAE AW FP0).
Local Notation cm_gate :=
  (CM.cm_gate ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb Rf Rlen RS S16 HK ST Hfb HF SR
     HHM HAE AW AFU FP0).
Local Notation cm_exit :=
  (CM.cm_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb Rf Rlen RS S16 HK ST Hfb SR HHM
     HAE AW FP0).
Local Notation cm_flag_upd := (CM.cm_flag_upd f len S FS fb Rf Rlen HK Hfb).
Local Notation cm_FB := (CM.cm_FB tp m f len S FS fb Rf Rlen HK Hfb HF HAE AFU FP0).
Local Notation cm_AF := (CM.cm_AF tp m f len S FS fb Rf Rlen S16 HK Hfb HF HHM HAE AFU FP0).
Local Notation cm_parse_addr := (CM.cm_parse_addr f len S fb Rf Rlen Hfb).
Local Notation cm_miss_short := (CM.cm_miss_short len fb).
Local Notation cm_miss_hdr := (CM.cm_miss_hdr len fb).
Local Notation sh_out_app := (CM.sh_out_app f len S fb Rf Rlen Hfb).

(* ---------------------------------------------------------------------------------------------------------- *)
(* The post predicates of the stretch ends: the source's continuation hypotheses (cmKB / cmPB / cmMiss and the
   premises of cm_exit), read as predicates on the state at the boundary. *)

(* 0x845dc, the gate: cmKB's state. The frame parameters are parameters of the predicate (cmP-brief.md), so a lift
   under a footprint that authorizes only the walk's own frame can discharge them. *)
Definition cmKBP (fr sp2 jj nn : Z) : machine_state -> Prop := fun ms =>
  exists (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    ms = MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
                 ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
                 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
            F (Z_to_bv 64 0x845dc) fc None mc (seg_rom rsegs)
    /\ cmInv fr sp2 jj nn mc.

(* 0x84684, the reac_ctrl_parse call (before the jal executes): cmPB's state. *)
Definition cmPBP (fr sp2 jj nn : Z) : machine_state -> Prop := fun ms =>
  exists (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    ms = MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
                 (Z_to_bv 64 f) (Z_to_bv 64 len) (Z_to_bv 64 (fr + 32)) ra3 ra4 ra5 ra6 ra7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
                 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
            F (Z_to_bv 64 0x84684) fc None mc (seg_rom rsegs)
    /\ 50 <= len /\ cp_v fb 12 = 0x88 /\ cp_v fb 13 = 0x19 /\ cp_v fb 16 = 0xcd /\ cp_v fb 17 = 0xea
    /\ cmInv fr sp2 jj nn mc /\ addressable mc (fr + 32) 36.

(* 0x84720, the catalogue-miss tail: cmMiss's state. *)
Definition cmMissP (fr sp2 jj nn : Z) : machine_state -> Prop := fun ms =>
  exists (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    ms = MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
                 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
                 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
            F (Z_to_bv 64 0x84720) fc None mc (seg_rom rsegs)
    /\ want CM_T len fb = 0 /\ cmInv fr sp2 jj nn mc.

(* 0x84724, the exit cut: the state cm_exit runs from. *)
Definition cmXCP (fr sp2 jj nn : Z) : machine_state -> Prop := fun ms =>
  exists (r : Z) (mc : word -> option byte)
         (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
    ms = MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
                 (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x84724) fc None mc (seg_rom rsegs)
    /\ r = want CM_T len fb /\ cmInv fr sp2 jj nn mc.

(* The gate leaves by the parse call or by the miss tail. *)
Definition cmGP (fr sp2 jj nn : Z) : machine_state -> Prop :=
  fun ms => cmPBP fr sp2 jj nn ms \/ cmMissP fr sp2 jj nn ms.
(* ---------------------------------------------------------------------------------------------------------- *)
(* The source's file-local tactics over StepF's evtF goals (the only change: the evt pattern becomes the evtF one,
   so StepF's step / store_done fire; the bodies are those of reac_box_catalogue_match.v). *)

Ltac steps_until_if :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

Ltac chk_core X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evtF ?segs ?RNG0 ?Q (MS ?R ?F0 (if _ then _ else ?B) ?fc0 ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RNG0 Q (MS (bvmap_set r rr R) F0 B fc0 rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_land7; extra X;
          step;
          let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
          first [ rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 1) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 1 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 3) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 3 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]) ];
          clear MB; bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac pre_sr X RX := step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_shr3.
Ltac no_extra X := idtac.

(* The source's cm_hdr_out (a file-local Ltac of its Section, so not exported): a side-stack header byte is apart
   from the side-arm footprint. Body unchanged. *)
Ltac cm_hdr_out HFSapp HHm8 :=
  cbn [outside]; unfold fs_hint, fs_flag, fs_M in *; cbn [Z.of_nat] in *;
  repeat first [ change (2 ^ 15) with 32768 in *
               | change (2 ^ (15 - 0)) with 32768 in *
               | change (2 ^ (14 - 0)) with 16384 in *
               | change (2 ^ (15 - 1)) with 16384 in *
               | change (2 ^ (14 - 1)) with 8192 in *
               | change (2 ^ (15 - 2)) with 8192 in * ];
  repeat split; try exact I;
  first
    [ lia
    | match goal with
      | |- ~ (shadow_addr ?frr <= ?xx < _) =>
          let A := fresh "A" in let B := fresh "B" in intros [A B];
          pose proof (acl_sh_out xx frr (frr + 8 * 32) ltac:(apply HFSapp; unfold FS_SIZE; lia)
                        ltac:(lia) ltac:(unfold APPMEM_END; lia)) as Hso;
          rewrite (cm_sh_add8 frr 32 HHm8) in Hso; apply Hso; split; [exact A | exact B]
      end ].

Ltac cm_wv :=
  let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  match goal with
  | |- wview _ _ (wa ?x) <> None =>
    first
      [ match goal with H : forall a, _ -> wview rsegs m (wa a) <> None |- _ => apply H; lia end
      | match goal with H : forall k, 0 <= k < 192 -> wview rsegs m (wa (?fr + k)) <> None |- _ =>
          replace x with (fr + (x - fr)) by lia; apply H; lia end
      | match goal with H : forall k, 0 <= k < 24 -> wview rsegs m (wa (?s + k)) <> None |- _ =>
          replace x with (s + (x - s)) by lia; apply H; lia end ]
  end.

Ltac cm_wst a n :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa a) n = true)
        by (eapply wv_store_ok;
            [ cm_wv | eassumption
            | try unfold shadow_addr; try unfold ASAN_K; Z.div_mod_to_equations; lia
            | try unfold shadow_addr; try unfold ASAN_K; Z.div_mod_to_equations; lia ])
  end.

Ltac cm_keep HB :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F0 ?pc ?fc0 ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
      let E := addr_expr a in
      change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs);
      assert (HB : bytes_at segs (write_to_mem mm (wa E) bs) E bs)
        by (apply bytes_at_write_same; first [simpl_sizes | cbn [length]]; lia);
      store_done
  end.

(* ---------------------------------------------------------------------------------------------------------- *)
(* (1) 0x84538 -> 0x845dc: the header run of cm_header, by its script over StepF.
   Accesses: the 8-byte store of s7 at CA + 24, the three 8-byte header words at fr, fr + 8, fr + 16, and the 24
   1-byte shadow stores at fr / 8 + ASAN_K + 0..23. *)
Lemma cm_header_F : forall (RNG : footprint) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rt3 rt4 rt5 rt6 : word),
  rng RNG (CA + 24) 8 -> rng RNG fr 24 -> rng RNG (fr / 8 + ASAN_K) 24 ->
  cmInv fr sp2 jj nn mc ->
  evtF rsegs RNG (cmKBP fr sp2 jj nn)
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             rs6 (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x84538) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rt3 rt4 rt5 rt6
    RCA RFR RSH INV.
  (* cm_header_F_on (SR gives SR_on, cmInv gives cmInv_on); its post cmKBP_on gives cmKBP by cmInv_of_on. *)
  eapply evtF_mono.
  { eapply (cm_header_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb); try eassumption.
    - exact (shadow_rw_on_of_shadow_rw _ m SR).
    - eapply cmInv_on_of_cmInv; exact INV. }
  intros ms' HP. unfold cmKBP_on in HP. unfold cmKBP.
  destruct HP as (mc' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & E & INV').
  exists mc', w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15.
  split; [exact E | eapply cmInv_of_on; [exact SR | exact INV']].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* (2a) 0x84508 -> 0x845dc, RE-BASED (the form the cgif-form walk uses, rebase-interfaces.md
   section 2.1 (a working note, not in this delivery)): the start memory is the base m (the return memory of the allocator event), x1 is free, and the
   invariant at the base replaces the allocator post's fake-frame arm and the pre-call facts that the source's
   script consumes only to build that invariant (rd_mono_list / rd_mono_trans / wmono_trans, cm_flag_upd,
   cm_mk_inv). Body: the four steps 0x84508 `mv s2,a0`, `j 84514`, `mv s7,s2`, `bnez s2,84538` (taken, fr <> 0),
   then cm_header_F. This is the source script with its post-call derivation deleted, not a re-run of it. *)
Lemma cm_resume_rb_F : forall (RNG : footprint) (jj : Z)
    (rr u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
  0 <= jj < fs_M 2 ->
  rng RNG (CA + 24) 8 -> rng RNG (fs_frame FS 2 jj) 24 -> rng RNG (fs_frame FS 2 jj / 8 + ASAN_K) 24 ->
  cmInv (fs_frame FS 2 jj) CA jj 1 m ->
  evtF rsegs RNG (cmKBP (fs_frame FS 2 jj) CA jj 1)
    (MS (mkR rr (Z_to_bv 64 CA) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             (Z_to_bv 64 (fs_frame FS 2 jj)) x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84508) fc None m (seg_rom rsegs)).
Proof.
  intros RNG jj rr u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 Hjj RCA RFR RSH INV.
  eapply evtF_mono.
  { eapply (cm_resume_rb_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb); try eassumption.
    - exact (shadow_rw_on_of_shadow_rw _ m SR).
    - eapply cmInv_on_of_cmInv; exact INV. }
  intros ms' HP. unfold cmKBP_on in HP. unfold cmKBP.
  destruct HP as (mc' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & E & INV').
  exists mc', w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15.
  split; [exact E | eapply cmInv_of_on; [exact SR | exact INV']].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* (2) 0x84508 -> 0x845dc: the return of __asan_stack_malloc_2 (side-stack arm), by the tail of cm_entry's script
   after its evt_cut on the allocator contract, then cm_header_F. The premises are the allocator post's fake-frame
   arm at the return, plus the facts the entry stretch (S1) carries to the call: the pre-call memory m0 relative to
   m, the saves of the frame, and the class-2 hint and flag array at m0. *)
Lemma cm_resume_F : forall (RNG : footprint) (m0 m2 : word -> option byte) (h h2 a0 : word)
    (flags : list byte) (ii : Z) (u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
  rng RNG (CA + 24) 8 ->
  rng RNG (fs_frame FS 2 ((bv_unsigned h + ii) mod fs_M 2)) 24 ->
  rng RNG (fs_frame FS 2 ((bv_unsigned h + ii) mod fs_M 2) / 8 + ASAN_K) 24 ->
  munch [(S - 9136, S)] m m0 -> wmono rsegs m m0 -> rd_mono m m0 ->
  rw_cells rsegs m0 (S - 96) cmSAVES ->
  bytes_at rsegs m0 (fs_hint FS 2) (le8 h) ->
  bytes_at rsegs m0 (fs_flag FS 2 0) flags -> Z.of_nat (length flags) = fs_M 2 ->
  Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags ->
  wmono rsegs m0 m2 -> mem_inv rsegs m2 -> stk rsegs m2 (S - 9136) CA -> fs_place m2 FS ->
  bytes_at rsegs m2 (fs_hint FS 2) (le8 h2) ->
  0 <= ii < fs_M 2 ->
  (forall i', 0 <= i' < ii -> nth_error flags (Z.to_nat ((bv_unsigned h + i') mod fs_M 2)) = Some (Z_to_bv 8 1)) ->
  nth_error flags (Z.to_nat ((bv_unsigned h + ii) mod fs_M 2)) = Some (Z_to_bv 8 0) ->
  asan_stack_malloc_frame 2 ASAN_STACK_MALLOC_K (Z_to_bv 64 CA) 192 FS
    ((bv_unsigned h + ii) mod fs_M 2) a0 m0 m2 ->
  evtF rsegs RNG (cmKBP (fs_frame FS 2 ((bv_unsigned h + ii) mod fs_M 2)) CA
                        ((bv_unsigned h + ii) mod fs_M 2) 1)
    (MS (mkR (Z_to_bv 64 0x84508) (Z_to_bv 64 CA) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             a0 x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K) s6 s7 s8 s9 s10 s11
             u3 u4 u5 u6)
         F (Z_to_bv 64 0x84508) fc None m2 (seg_rom rsegs)).
Proof.
  intros RNG m0 m2 h h2 a0 flags ii u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6
    RCA RFR RSH MU WM RM FR HH2 HF2 HFl2 HFb2 WM2 MI2 ST2 FSP2 HH2' Hii0 Hiipre Hiinth FRM.
  eapply evtF_mono.
  { eapply (cm_resume_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb); try eassumption.
    exact (shadow_rw_on_of_shadow_rw _ m SR). }
  intros ms' HP. unfold cmKBP_on in HP. unfold cmKBP.
  destruct HP as (mc' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & E & INV').
  exists mc', w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15.
  split; [exact E | eapply cmInv_of_on; [exact SR | exact INV']].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* (3) 0x845dc -> 0x84684 (the parse call) or -> 0x84720 (the miss tail): cm_gate's script over StepF.
   Accesses: the four header bytes f + 12, f + 13, f + 16, f + 17 and their shadow bytes (both named by the
   lemma's own premises HF / AFU through cmInv), and the five 1-byte shadow stores at fr / 8 + ASAN_K + 4..8. *)
Lemma cm_gate_F : forall (RNG : footprint) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  (50 <= len -> rng RNG f 50) ->
  (50 <= len -> rng RNG (f / 8 + ASAN_K) ((f + 49) / 8 - f / 8 + 1)) ->
  rng RNG (fr / 8 + ASAN_K) 24 ->
  cmInv fr sp2 jj nn mc ->
  evtF rsegs RNG (cmGP fr sp2 jj nn)
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x845dc) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 RDAT RSHD RSH INV.
  eapply evtF_mono.
  { eapply (cm_gate_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb); try eassumption.
    - exact (shadow_rw_on_of_shadow_rw _ m SR).
    - eapply cmInv_on_of_cmInv; exact INV. }
  intros ms' HP. unfold cmGP_on in HP. unfold cmGP. destruct HP as [HP|HP]; [left | right].
  - unfold cmPBP_on in HP. unfold cmPBP.
    destruct HP as (mc' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13
                    & E & L & E12 & E13 & E16 & E17 & INV' & AD').
    exists mc', w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13.
    split; [exact E|]. split; [exact L|]. split; [exact E12|]. split; [exact E13|]. split; [exact E16|].
    split; [exact E17|]. split; [eapply cmInv_of_on; [exact SR | exact INV'] | exact AD'].
  - unfold cmMissP_on in HP. unfold cmMissP.
    destruct HP as (mc' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16
                    & E & HW & INV').
    exists mc', w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16.
    split; [exact E|]. split; [exact HW | eapply cmInv_of_on; [exact SR | exact INV']].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* (4) 0x84720 -> 0x84724: the first step of cm_miss_holds (`li s3,0`), which the source then hands to cm_exit.
   The step touches no memory, so it adds no rng premise. *)
Lemma cm_miss_F : forall (RNG : footprint) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  want CM_T len fb = 0 -> cmInv fr sp2 jj nn mc ->
  evtF rsegs RNG (cmXCP fr sp2 jj nn)
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x84720) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 Hw INVk.
  step.
  apply evtF_done. unfold cmXCP.
  exists 0. exists mc. do 21 eexists. split; [reflexivity|].
  split; [symmetry; exact Hw | exact INVk].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* The old (Exec.evt) statements of the four runs, re-derived from the footprint forms with ExecF.rng_all: the
   check that each _F statement is the old one plus footprint premises, nothing weaker. *)

Lemma cm_header_of_F : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rt3 rt4 rt5 rt6 : word),
  cmKB Q -> cmInv fr sp2 jj nn mc ->
  evt rsegs Q
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             rs6 (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x84538) fc None mc (seg_rom rsegs)).
Proof.
  intros Q fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rt3 rt4 rt5 rt6 K INV.
  eapply (cm_header_of_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb); try eassumption.
  - exact (shadow_rw_on_of_shadow_rw _ m SR).
  - intros fr' sp2' jj' nn' mc' w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 INV'.
    apply (K fr' sp2' jj' nn' mc' w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15).
    eapply cmInv_of_on; [exact SR | exact INV'].
  - eapply cmInv_on_of_cmInv; exact INV.
Qed.

Lemma cm_resume_of_F : forall (m0 m2 : word -> option byte) (h h2 a0 : word)
    (flags : list byte) (ii : Z) (u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
  munch [(S - 9136, S)] m m0 -> wmono rsegs m m0 -> rd_mono m m0 ->
  rw_cells rsegs m0 (S - 96) cmSAVES ->
  bytes_at rsegs m0 (fs_hint FS 2) (le8 h) ->
  bytes_at rsegs m0 (fs_flag FS 2 0) flags -> Z.of_nat (length flags) = fs_M 2 ->
  Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags ->
  wmono rsegs m0 m2 -> mem_inv rsegs m2 -> stk rsegs m2 (S - 9136) CA -> fs_place m2 FS ->
  bytes_at rsegs m2 (fs_hint FS 2) (le8 h2) ->
  0 <= ii < fs_M 2 ->
  (forall i', 0 <= i' < ii -> nth_error flags (Z.to_nat ((bv_unsigned h + i') mod fs_M 2)) = Some (Z_to_bv 8 1)) ->
  nth_error flags (Z.to_nat ((bv_unsigned h + ii) mod fs_M 2)) = Some (Z_to_bv 8 0) ->
  asan_stack_malloc_frame 2 ASAN_STACK_MALLOC_K (Z_to_bv 64 CA) 192 FS
    ((bv_unsigned h + ii) mod fs_M 2) a0 m0 m2 ->
  evt rsegs (cmKBP (fs_frame FS 2 ((bv_unsigned h + ii) mod fs_M 2)) CA
                   ((bv_unsigned h + ii) mod fs_M 2) 1)
    (MS (mkR (Z_to_bv 64 0x84508) (Z_to_bv 64 CA) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             a0 x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K) s6 s7 s8 s9 s10 s11
             u3 u4 u5 u6)
         F (Z_to_bv 64 0x84508) fc None m2 (seg_rom rsegs)).
Proof.
  intros m0 m2 h h2 a0 flags ii u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6
    MU WM RM FR HH2 HF2 HFl2 HFb2 WM2 MI2 ST2 FSP2 HH2' Hii0 Hiipre Hiinth FRM.
  eapply evt_mono.
  { eapply (cm_resume_of_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb); try eassumption.
    exact (shadow_rw_on_of_shadow_rw _ m SR). }
  intros ms' HP. unfold cmKBP_on in HP. unfold cmKBP.
  destruct HP as (mc' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & E & INV').
  exists mc', w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15.
  split; [exact E | eapply cmInv_of_on; [exact SR | exact INV']].
Qed.

Lemma cm_gate_of_F : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  cmPB Q -> cmMiss Q -> cmInv fr sp2 jj nn mc ->
  evt rsegs Q
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x845dc) fc None mc (seg_rom rsegs)).
Proof.
  intros Q fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 KP KM INV.
  eapply (cm_gate_of_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb); try eassumption.
  - exact (shadow_rw_on_of_shadow_rw _ m SR).
  - intros fr' sp2' jj' nn' mc' w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 L E12 E13 E16 E17 INV' AD'.
    apply (KP fr' sp2' jj' nn' mc' w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 L E12 E13 E16 E17);
      [eapply cmInv_of_on; [exact SR | exact INV'] | exact AD'].
  - intros fr' sp2' jj' nn' mc' w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 HW INV'.
    apply (KM fr' sp2' jj' nn' mc' w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 HW).
    eapply cmInv_of_on; [exact SR | exact INV'].
  - eapply cmInv_on_of_cmInv; exact INV.
Qed.

Lemma cm_miss_of_F : cmMiss cmPost.
Proof.
  intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 Hw INVk.
  eapply evt_mono.
  { eapply (cm_miss_of_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb); try eassumption.
    - exact (shadow_rw_on_of_shadow_rw _ m SR).
    - eapply cmInv_on_of_cmInv; exact INVk. }
  intros ms' HP. eapply cmPost_of_on; [exact SR | exact HP].
Qed.

End MatchF.

(* ---------------------------------------------------------------------------------------------------------- *)
(* The two `jal` steps of this function that the cgif rules start after (rebase-interfaces.md section 2.5): each
   stretch stops BEFORE its jal, and the rule (aj_stack_malloc_atS / TPARSE) starts at the callee entry with ra
   set. One StepF step each; a jal makes no memory access, so neither takes an rng premise.
   Image: `84504: jal 3d8bc <__asan_stack_malloc_2>`, `84684: jal 83578 <reac_ctrl_parse>`. *)
Lemma cm_jal_sm2_F : forall (RNG : footprint) (Q : machine_state -> Prop)
    (x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mc : word -> option byte),
  Q (MS (mkR (Z_to_bv 64 0x84508) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x3d8bc) fc None mc (seg_rom rsegs)) ->
  evtF rsegs RNG Q
    (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x84504) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG Q x1 sp gp' tp' t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11'
    t3 t4 t5 t6 F' fc' mc HQ.
  step. apply evtF_done. exact HQ.
Qed.

Lemma cm_jal_parse_F : forall (RNG : footprint) (Q : machine_state -> Prop)
    (x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mc : word -> option byte),
  Q (MS (mkR (Z_to_bv 64 0x84688) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x83578) fc None mc (seg_rom rsegs)) ->
  evtF rsegs RNG Q
    (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x84684) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG Q x1 sp gp' tp' t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11'
    t3 t4 t5 t6 F' fc' mc HQ.
  step. apply evtF_done. exact HQ.
Qed.

(* Route (C): the assumptions of the `_on` stretches the glue uses. cm_jal_sm2_F / cm_jal_parse_F name no shadow fact
   (no `_on` twin). *)
Check cm_resume_rb_F_on.
Print Assumptions cm_resume_rb_F_on.
Check cm_gate_F_on.
Print Assumptions cm_gate_F_on.
Check cm_miss_F_on.
Print Assumptions cm_miss_F_on.
