(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Image.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl KInv KStep KLink KEv Prog
  MI_Tree MI_Inv MI_Contracts LB_Tables LB_Inv LB_Sum LB_Kernel LB_KCount LB_QM LB_StmtA LB_Raw Gap.
Import ListNotations.
Open Scope Z_scope.

Lemma zsum_nonneg' l : (forall x, In x l -> 0 <= x) -> 0 <= zsum l.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0020=15043033658.158311399062.5000001008SS2IH2H0".
induction l as [|a l IH]; intros H; cbn; [lia|]. pose proof (H a (or_introl eq_refl)). specialize (IH ltac:(intros x Hx; apply H; right; exact Hx)). unfold zsum in IH. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma CAP_lower P c : (forall c, 0 <= P c) -> 0 <= c -> 14 <= CAP P c.
Proof.
  intros HP Hc.
  assert (0 <= HOSTSTD P c).
  { unfold HOSTSTD. apply zsum_nonneg'. intros x Hx. apply in_map_iff in Hx as (c' & <- & Hc').
    Local Ltac2 Set LiaHints.tbl := fun () => "0060=15494552990.833548619532.944347020398.6469299344.6  5872385214.9 63375171198.600000400900?00H00K00PS2CMS1G1HS1H2H0S2Hc1H2H0S1HS3Hc'".
assert (G : 0 <= c' < 48) by (unfold guests in Hc'; cbn in Hc'; lia). cbn beta.
    destruct (bighost c' =? c); [| apply Z.le_refl]. pose proof (tab_basic_ok c' G) as (_ & CM & _).
    apply Z.div_pos; [| lia]. unfold CAP0. pose proof (HP c'). destruct (c' <=? 23); lia. }
  unfold CAP, CAP0. pose proof (HP c). destruct (c <=? 23); lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma NCAP_lower P : (forall c, 0 <= P c) -> 4 <= NCAP P.
Proof.
  intros HP. unfold NCAP, NG.
  assert (0 <= zsum (map (fun c => (CAP P c + 32) / cmax c + 160) classes)).
  { apply zsum_nonneg'. intros x Hx. apply in_map_iff in Hx as (c & <- & Hc). apply In_classes in Hc. cbn beta.
    pose proof (tab_basic_ok c Hc) as (_ & CM & _). Local Ltac2 Set LiaHints.tbl := fun () => "0050=18896237181.419320801509.623318993981.65964073780.7 68390340120.500000600:00=00A00ES1H2H0S2CMS1HS2H0S2Hc".
pose proof (CAP_lower P c HP ltac:(lia)).
    assert (0 <= (CAP P c + 32) / cmax c) by (apply Z.div_pos; lia). lia. }
  pose proof (HP 63). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma SINV_minit secret resv atop : SINV x0 (minit secret resv atop) [].
Proof.
  constructor; cbn -[Z.mul Z.add Z.le Z.lt]; try (intros *; intros HH; rewrite lookup_empty in HH; discriminate).
  - intros k [].
  - intros c. unfold MIS, zcount, zlen. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0040=34773373609.449499753102.461711929960.39574675323.5 000001004005006SS1HSS".
lia.
  - intros c Hc. unfold nsc, gmetas, groups_l. cbn [s_groups minit]. rewrite map_to_list_empty. cbn. lia.
  - unfold apages, ncarved, regions_l. cbn [s_regions s_metas minit]. rewrite !map_to_list_empty. unfold zlen. cbn. lia.
  - intros H. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma gcnt_minit secret resv atop c : gcnt (minit secret resv atop) c = 0.
Proof. unfold gcnt. cbn [s_groups minit]. rewrite map_to_list_empty. reflexivity. Qed.

Lemma AQ_minit P secret resv atop : (forall c, 0 <= P c) -> PQOK P -> AQ (minit secret resv atop) [] P.
Proof.
  intros HP PQ. constructor.
  - intros c Hc. unfold LR, zcount, zlen. cbn. apply HP.
  - intros c Hc. rewrite gcnt_minit. Local Ltac2 Set LiaHints.tbl := fun () => "0030=20992340560.723318993981.968390425458.800000300600:S1HS1HS2Hc".
pose proof (CAP_lower P c HP ltac:(lia)). lia.
  - unfold n63, zcount, zlen. cbn. apply HP.
  - unfold ncarved. cbn [s_metas minit]. rewrite map_to_list_empty. pose proof (NCAP_lower P HP). unfold zlen. cbn. lia.
  - exact HP.
  - exact PQ.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma reserved_top_ge' : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. Local Ltac2 Set LiaHints.tbl := fun () => "0020=16825179538.425708821631.6000001005SS2IH".
destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem QI_init : forall P segs brk0 mbase sp lim inp atop,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->            (* [comment removed for export] *)
  atop = bv_unsigned sp - stack_max_size ->                     (* [comment removed for export] *)
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 2^34 + 8 * PGSZ <= FLOOR ->
  live_bytes (segments_reserved segs) <= 2^30 -> 2^31 <= lim ->
  (forall c, 0 <= P c) -> PQOK P -> PHI P <= LBUDGET ->
  QI [] P (ps_init (reservedZ segs) atop) (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros P segs brk0 mbase sp lim inp atop (Hlo & Hhi & Hal) Hpos Hsp Eatop Hceil Hfloor Hresv Hlim HP PQ HPHI. Local Ltac2 Set LiaHints.tbl := fun () => "0090>12584768545.2513807164177.2514152173418.2216154904229.2527547058782.2533668031574.2853517065302.2355956085492.256159675390.21 00000100S00^00j00k01201301901?SS3Hlo3Hhi3Hal4Hpos3Hsp5Eatop5HceilS3Hsp5EatopS3Hhi6HfloorSS3Hlo1HSS4HlimS4HPHI".
split; [| unfold R63X, zsum; cbn; lia].
  pose proof alloc_ceiling_lo_val as Hclo.
  assert (Hat : 0 < atop <= atop_hi) by (unfold atop_hi, sp_window_lo, sp_window_hi, stack_max_size in *; lia).
  exists (minit 0 (reservedZ segs) atop), (led_init (reservedZ segs) atop), [], (fun _ => []).
  split; [reflexivity|]. split; [apply INVL_init; [lia| exact Hat]|]. split; [apply SINV_minit|]. split; [apply AQ_minit; [exact HP| exact PQ]|].
  assert (Evm : m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)
                = mkVmMapsFull (segments_reserved segs) [] [] brk0 brk0 lim mbase sp) by reflexivity.
  assert (Eh : m_halted (init_model (segments_reserved segs) brk0 mbase sp lim inp) = None) by reflexivity.
  split; [| split; [| split; [| apply Permutation_refl]]].
  - constructor; rewrite ?Evm; cbn -[Z.pow Z.mul Z.add Z.sub init_model alloc_top].
    + apply minv_init. exact Hsp.
    + exact Eh.
    + split; [intros e []| apply pwdisj_nil].
    + reflexivity.
    + intros e Hin. pose proof (reserved_top_ge' _ _ Hin). unfold ehi. lia.
    + unfold PGSZ in *. unfold page_size in Hal. unfold alloc_ceiling_lo, sp_window_lo, stack_max_size in *. lia.
    + intros b l [].
    + intros b l k [].
    + apply List.NoDup_nil.
    + intros b l H. discriminate.
    + split; reflexivity.
    + unfold alloc_top. cbn [vm_init_sp]. exact Eatop.
  - unfold LI, gm, BB. rewrite Evm. cbn. lia.
  - split; [| split].
    + rewrite Evm. unfold kcnt, lcnt. cbn. lia.
    + unfold LNstat. rewrite Evm. cbn -[Z.pow Z.mul Z.add]. unfold PGSZ in *. split; [lia|]. split; [lia| exact Hresv].
    + intros b l H. discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
