(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "prod"; "list"; "app"; "pair"; "bool"; "cons"; "length"; "true"; "false"; "fst"; "negb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "eqb"; "modulo"; "sub"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "live_bytes"; "m_vmmaps"; "Model"; "vm_maps"; "vm_reserved"; "m_vm_materialized"; "vm_init_sp"; "vm_limit"; "with_vmmaps"; "iv_subtract"; "map_remove"; "maps_subtract"; "maps_subtract_all"; "page_size"; "region_free"; "vm_backing_used"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "vm_room"; "vm_pot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap"; "disjoint"; "zpair"; "pairwise"; "ledger_disciplined"; "total"; "entry_ok"; "ledger_budget_ok"; "page_len"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_n"; "mmap_none_vm"; "mmap_place_ok"; "mmap_place_ok_none"; "mmap_rw_vm"; "munmap_model"; "@Stdlib.Lists.List"; "filter"; "In"; "@Corelib.Init.Peano"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noreserve_b"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_budget_ok"; "mprotect_model_next"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymSoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocLayout FreeGap ContractDrv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma live_bytes_total : ltac2:(tb__ "0|2|
S2S1ScQ40A1M0G0A2M1A1S15S0S18R1A1S2eS32G1S1S0S0A2S2bR1A4A1A3Fl;").
Proof.
  induction l as [|[a s] t IH]; [reflexivity|]. cbn [live_bytes map]. unfold total in *. cbn. rewrite IH. reflexivity.
Qed.

Lemma live_bytes_app : ltac2:(tb__ "0|3|
S2S1ScQ40A1M0G0A2M1A1M2G2S15S0S18S3G1R2R1A3A1SfS18R2A1S18R1A1A2A3Fl2;Fl1;").
Proof. intros. rewrite !live_bytes_total, map_app, total_app. reflexivity. Qed.

Lemma live_bytes_nonneg : ltac2:(tb__ "0|1|
S2S1ScQ40A1M0G0A2A1SeZ0S18R1A1A2Fl;").
Proof.
  induction l as [|[a s] t IH]; cbn [live_bytes]; [lia|]. pose proof (urange s). lia.
Qed.

Lemma two64_eq : bv_modulus 64 = 2 ^ 64.
Proof. reflexivity. Qed.

Lemma live_bytes_iv_subtract : ltac2:(tb__ "0|2|
ScQ40M0A1M1G1S0S0SeR2R1A2SeS18S21R5R4R3R2A4A1SdG0R4A2A2F_;Fhi;Flo;Fsz;Fa;").
Proof.
  intros a sz lo hi Hle. unfold iv_subtract.
  pose proof (urange a) as Ha. pose proof (urange sz) as Hs.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2; cbn [live_bytes app];
    try apply Z.ltb_lt in E1; try apply Z.ltb_ge in E1; try apply Z.ltb_lt in E2; try apply Z.ltb_ge in E2;
    rewrite ?Z_to_bv_unsigned, ?bv_wrap_small by (rewrite two64_eq; lia); lia.
Qed.

Lemma live_bytes_subtract : ltac2:(tb__ "0|1|
S2S1ScQ40A1M0G0A2A1S0S0SeR2R1A2SeS18S23R4R3R2A3A1S18R4A1A2F_;Fhi;Flo;Fmaps;").
Proof.
  induction maps as [|[a s] t IH]; intros lo hi Hle; cbn [maps_subtract live_bytes]; [lia|].
  rewrite live_bytes_app. pose proof (live_bytes_iv_subtract a s lo hi Hle). specialize (IH lo hi Hle). lia.
Qed.

Lemma live_bytes_subtract_all : ltac2:(tb__ "0|2|
S2S1ScQ40A1M0G0A2A1M1G1SeS18S24R1R2A2A1S18R1A1A2Fmaps;Fcuts;").
Proof.
  induction cuts as [|[a n] t IH]; intros maps; cbn [maps_subtract_all]; [lia|].
  etransitivity; [apply IH|]. apply live_bytes_subtract. pose proof (urange n). lia.
Qed.

Lemma total_zpair_nonneg : ltac2:(tb__ "0|2|
S2S1ScQ40A1M0G0A2M1A1SeZ0S2eS32G1S1S0S0A2S2bR1A4A1A2Fl;").
Proof. intros l. rewrite <- live_bytes_total. apply live_bytes_nonneg. Qed.

Lemma PGSZ_page_size : PGSZ = page_size.
Proof. reflexivity. Qed.

Lemma vm_backing_used_le_pot : ltac2:(tb__ "0|0|
S1aSeS27R1A1S29R1A1A2Fmd;").
Proof.
  intros md. unfold vm_backing_used, vm_pot, vm_backed_maps.
  rewrite map_app, total_app, PGSZ_page_size.
  pose proof (live_bytes_subtract_all (m_vm_lazy md) (maps_subtract_all (vm_maps (m_vmmaps md)) (vm_noaccess (m_vmmaps md)))).
  pose proof (live_bytes_subtract_all (vm_noaccess (m_vmmaps md)) (vm_maps (m_vmmaps md))).
  pose proof (total_zpair_nonneg (vm_reserved (m_vmmaps md))).
  rewrite <- (live_bytes_total (vm_maps (m_vmmaps md))). lia.
Qed.

Lemma vm_room_vmmaps_le : ltac2:(tb__ "0|5|
S1aS1aS0S15S2S1ScQ40A1M0G0A2A1M1S1cS19R2A1A1S1cS19R3A1M2A1A3S15G1S1bG2A1S1bS19R4A1M3A1A3S15S0S1fG3A1S1fS19R5A1M4A1A3S15G0S1eG4A1S1eS19R6A1A1A3S3cS7G0S1dR6A1A2S7G0S1dR7A1A2A2S28R8R6A2S28R8R7A2F_;F_;F_;F_;F_;F_;FX;Fmd';Fmd;").
Proof.
  intros md md' X Hr Hm Hl Hsp Hlen (D & H0 & HP & HL & HT). unfold vm_room, vm_pot in *.
  rewrite Hr, Hm, Hl. split; [exact D|]. split; [exact H0|]. split; [|split; [exact HL| unfold alloc_top in *; rewrite Hsp; exact HT]].
  apply Nat2Z.inj_le in Hlen. unfold PGSZ in *.
  set (T := total _) in *. nia.
Qed.

Lemma mmap_nZ_page_len : ltac2:(tb__ "0|1|
ScQ40M0A1S10Z0SdG0R1A2A2S31S33R2A1A1F_;Flen;").
Proof.
  intros len Hl. unfold mmap_nZ, page_len, PG. split.
  - pose proof (page_round_up_Z_ge (bv_unsigned len)). lia.
  - apply page_round_up_Z_aligned.
Qed.

Lemma disciplined_budget : ltac2:(tb__ "0|2|
S2S1ScQ40A1M0G0A2M1A1S0S0S2dR3A1SeZ0R3A2SeSfS2eS32G1S1S0S0A2S2bR5A4A1R4A2R3A2SeR4S11Z2Z28A2A2S30R7A1F_;F_;F_;F_;Flim;FX;Fmaps;").
Proof.
  intros maps X lim [Hent _] HX HT HL. unfold ledger_budget_ok, BUDGET.
  etransitivity; [apply total_filter_le|].
  - intros e He. apply in_map_iff in He as (e' & <- & He'). destruct (Hent e' He') as (_ & [Hp _] & _). exact Hp.
  - lia.
Qed.

Lemma disciplined_cons : ltac2:(tb__ "0|3|
ScQ40M0A1M1G1S2S1G1G1A2M2A1S2dR1A1S2fS4S0S0SdG0R4A2SdG0R3A2A4A1G2S3bG2R1R4A3S2aS4S0S0SdG0R7A2SdG0R6A2A4S2bR2A1A2F_;Fe;S2dS6G2S4G1G1R6R5A4R4A3A1F_;F_;F_;Fmaps;Fn;Fa;").
Proof.
  intros a n maps [Hent Hpw] He Hd. split.
  - intros e [<-|Hin]; [exact He | exact (Hent e Hin)].
  - cbn. split; [|exact Hpw]. intros y Hy. apply in_map_iff in Hy as (e & <- & Hin). exact (Hd e Hin).
Qed.

Lemma pairwise_disjoint_middle : ltac2:(tb__ "0|2|
S2S1S0S0A2M0A1M1G0G1S2cG0S2aS6G0R2S3G0R3R1A3A3A3S2cG0S2aS3G0R4S6G0R3R2A3A3A3F_;Fl2;Fx;Fl1;").
Proof.
  induction l1 as [|y t IH]; intros x l2 H; cbn in *; [exact H|].
  destruct H as [Hx [Hy Ht]]. split.
  - intros z Hz. apply in_app_iff in Hz as [Hz|[<-|Hz]].
    + apply Hy. apply in_app_iff. left; exact Hz.
    + specialize (Hx y ltac:(left; reflexivity)). unfold FreeGap.disjoint in *. lia.
    + apply Hy. apply in_app_iff. right; exact Hz.
  - apply IH. split; [|exact Ht]. intros z Hz. apply Hx. right; exact Hz.
Qed.

Lemma disciplined_middle : ltac2:(tb__ "0|3|
S2S1ScQ40A1M0G0A2M1A1M2G0G0G2S2dS6G1S4G0G0R3R2A4S3G1R4R1A3A3A1S2dS3G1R5S6G1S4G0G0R4R3A4R2A3A3A1F_;Fmaps;Fn;Fa;Fres;").
Proof.
  intros res a n maps [Hent Hpw]. split.
  - intros e He. apply Hent. apply in_app_iff in He as [He|[<-|He]]; [right; apply in_app_iff; auto | left; reflexivity | right; apply in_app_iff; auto].
  - rewrite map_app. cbn [map]. apply pairwise_disjoint_middle. rewrite <- map_app. exact Hpw.
Qed.

Theorem vm_room_grant : ltac2:(tb__ "0|a|
S1aS0ScQ40M0A1M1S28R3R2A2S10Z0M2SdG0R2A2A2SeS33R3A1S11Z2Z20A2A2SeS33R4A1R5A2S17G1G1S16S15S0S13SdG0R1A2M3S25A2G2A3S16S10G2G3A2S16SeZ2aaaaaaab000G3A2S16SeSfG3S33R6A1M4A2Z7fff7f800000A2S16S15S0SdG0S34R6A1M5A2G4A3S16S15S5S26S3S1G1G1A2M6S1cS19R8A1M7A1S1bG7A1A3R1G5A3S8A3S16G6S3bG6R1S3G6S1cS19R9A1M8A1S1bG8A1A3A3S2aS4S0S0SdG0R3A2S33R8A1A4S2bR2A1A2F_;Fe;S16G1G1S15S5S3dR1A1S9A3S36R3R2RbR9R4A5F_;Fflags;Fhint;S16G1S37R1R9R7R2A4Fhint;S16S28S20S38G7R6R1A3R8A2S14R7G4A2M9A2S28S20S35G7R6R1A3R8A2G9A2A2A2A2A2A2A2A2A2A2A2La;A2F_;F_;F_;F_;Flen;FX;Fmd;").
Proof.
  intros md X len HR Hlen H32 HX. pose proof HR as (D & H0 & HP & HL & HTOP).
  pose proof (mmap_nZ_page_len len Hlen) as Hpl. pose proof Hpl as [Hnpos Hnal]. unfold PG in Hnal.
  assert (HB : ledger_budget_ok (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md))).
  { eapply disciplined_budget; [exact D | exact H0 | | exact HL]. unfold vm_pot in HP. unfold PGSZ in HP. nia. }
  destruct (free_gap_exists_ledger _ _ D HB Hpl H32) as (aZ & W & Pal & HF & HC & Hpos & Hrf & Hdj).
  unfold F in HF. unfold CEIL in HC. unfold PG in Pal.
  assert (Ha : bv_unsigned (Z_to_bv 64 aZ) = aZ).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64_eq. lia. }
  assert (Hn : bv_unsigned (mmap_n len) = mmap_nZ len).
  { unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64_eq. lia. }
  assert (Hfl : 0x2aaaaaaab000 <= aZ) by lia.
  assert (Hceil : aZ + mmap_nZ len <= aceil_lo) by lia.
  assert (Hbud : vm_backing_used md + mmap_nZ len <= vm_limit (m_vmmaps md)).
  { pose proof (vm_backing_used_le_pot md). lia. }
  assert (Hent : entry_ok (aZ, mmap_nZ len)).
  { split; [left; exact W|]. split; [exact Hpl | exact H32]. }
  assert (Dnew : ledger_disciplined (vm_reserved (m_vmmaps md) ++ (Z_to_bv 64 aZ, mmap_n len) :: vm_maps (m_vmmaps md))).
  { apply disciplined_middle. apply disciplined_cons; [exact D | rewrite Ha, Hn; exact Hent | rewrite Ha, Hn; exact Hdj]. }
  assert (Hpot : forall h', vm_reserved h' = vm_reserved (m_vmmaps md) -> vm_maps h' = (Z_to_bv 64 aZ, mmap_n len) :: vm_maps (m_vmmaps md) ->
                 vm_limit h' = vm_limit (m_vmmaps md) -> vm_init_sp h' = vm_init_sp (m_vmmaps md) ->
                 vm_room (with_vmmaps h' md) (X - mmap_nZ len)).
  { intros h' Hr Hm Hl Hsp. unfold vm_room, vm_pot.
    change (m_vmmaps (with_vmmaps h' md)) with h'.
    change (m_vm_materialized (with_vmmaps h' md)) with (m_vm_materialized md).
    rewrite Hr, Hm, Hl. split; [exact Dnew|]. split; [lia|]. split; [|split; [exact HL|]].
    2:{ unfold alloc_top in *. rewrite Hsp. exact HTOP. }
    unfold vm_pot in HP. rewrite map_app, total_app in *. cbn [map].
    change (total ((zpair (Z_to_bv 64 aZ, mmap_n len)) :: map zpair (vm_maps (m_vmmaps md))))
      with (snd (zpair (Z_to_bv 64 aZ, mmap_n len)) + total (map zpair (vm_maps (m_vmmaps md)))).
    change ((zpair (Z_to_bv 64 aZ, mmap_n len)).2) with (bv_unsigned (mmap_n len)). rewrite Hn. lia. }
  exists (Z_to_bv 64 aZ). rewrite Ha. repeat match goal with |- _ /\ _ => split end; auto.
  - intros hint flags Hnr. unfold mmap_place_ok. rewrite Ha. repeat split; auto; [lia|].
    unfold mmap_noreserve_backed_ok. rewrite Hnr. apply Z.leb_le. exact Hbud.
  - intros hint. unfold mmap_place_ok_none. rewrite Ha. repeat split; auto. lia.
Qed.

Theorem vm_room_mprotect : ltac2:(tb__ "0|1|
S1aS0ScQ40A1M0G0S28R4R3A2S16S15S5S3eR5R3R2A3S8A3S28S3fR5R3R2A3R4A2A2F_;Fn;Faddr;FX;Fmd;").
Proof.
  intros md X addr n HR. pose proof HR as (D & H0 & HP & HL).
  assert (HR' : vm_room (mprotect_model_next md addr n) X).
  { eapply vm_room_vmmaps_le; [ | | | | | exact HR]; reflexivity. }
  split; [|exact HR'].
  unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
  pose proof (vm_backing_used_le_pot (mprotect_model_next md addr n)).
  destruct HR' as (_ & H0' & HP' & _). lia.
Qed.

Lemma pairwise_filter : ltac2:(tb__ "0|1|
S1S0S0A2M0S5F_;S2G0A1S2cG0S2aR1A3S2cG0S2aS3aG0R3R2A3A3F_;Fl;Ff;").
Proof.
  induction l as [|x t IH]; cbn; intros H; [exact I|].
  destruct H as [Hx Ht]. destruct (f x); cbn; [|apply IH; exact Ht].
  split; [|apply IH; exact Ht]. intros y Hy. apply filter_In in Hy as [Hy _]. exact (Hx y Hy).
Qed.

Lemma map_zpair_filter_base : ltac2:(tb__ "0|4|
S2S1ScQ40M0A1M1G1A2M2A1G1S15S2S1S0S0A2M3A1S32G2G3S2bS22R2R1A2A4S3aG3G3SbS12SaS0S0R1A3SdG0R2A2A2A1Lp;S32G2G3S2bR2A4A3A3Flo;Fmaps;").
Proof.
  intros maps lo. unfold map_remove. induction maps as [|[a s] t IH]; [reflexivity|].
  cbn [List.filter map fst]. unfold zpair at 2. cbn [fst snd].
  replace (Z.eqb (bv_unsigned a) (bv_unsigned lo)) with (bv_eqb a lo).
  2:{ unfold bv_eqb. destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned lo)) as [E|NE].
      - apply bv_eq in E. subst. destruct (decide (lo = lo)); [reflexivity|congruence].
      - destruct (decide (a = lo)) as [E'|NE']; [subst; lia|reflexivity]. }
  destruct (bv_eqb a lo); cbn [negb]; [exact IH|]. cbn [map]. rewrite IH. reflexivity.
Qed.

Lemma pairwise_app_filter : ltac2:(tb__ "0|2|
S1S0S0A2M0S5F_;S2G0A1M1G1S2cG0S2aS3G0R2R1A3A3S2cG0S2aS3G0R3S3aG0R4R2A3A3A3F_;Fl2;Fl1;Ff;").
Proof.
  induction l1 as [|x t IH]; intros l2 H; cbn in *; [apply pairwise_filter; exact H|].
  destruct H as [Hx Ht]. split; [|apply IH; exact Ht].
  intros y Hy. apply in_app_iff in Hy as [Hy|Hy]; [apply Hx; apply in_app_iff; left; exact Hy|].
  apply filter_In in Hy as [Hy _]. apply Hx; apply in_app_iff; right; exact Hy.
Qed.

Theorem vm_room_munmap : ltac2:(tb__ "0|1|
S1aS0ScQ40A1M0G0S28R4R3A2S28S39R5R3R2A3R4A2F_;Fn;Faddr;FX;Fmd;").
Proof.
  intros md X addr n (D & H0 & HP & HL & HT).
  set (md' := munmap_model md addr n).
  assert (Hr : vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md)) by reflexivity.
  assert (Hm : vm_maps (m_vmmaps md') = map_remove (vm_maps (m_vmmaps md)) addr) by reflexivity.
  assert (Hl : vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md)) by reflexivity.
  assert (Hmat : m_vm_materialized md'
                 = List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized md)) by reflexivity.
  unfold vm_room, vm_pot. rewrite Hr, Hm, Hl, Hmat. unfold vm_pot in HP.
  destruct D as [Hent Hpw].
  split; [|split; [exact H0 | split; [|split; [exact HL|exact HT]]]].
  - split.
    + intros e He. apply Hent. apply in_app_iff in He as [He|He]; apply in_app_iff; [left; exact He|right].
      unfold map_remove in He. apply filter_In in He as [He _]. exact He.
    + rewrite map_app, map_zpair_filter_base. apply pairwise_app_filter. rewrite <- map_app. exact Hpw.
  - rewrite map_app, total_app, map_zpair_filter_base. rewrite map_app, total_app in HP.
    assert (Hf : total (List.filter (fun p : Z * Z => negb (fst p =? bv_unsigned addr)) (map zpair (vm_maps (m_vmmaps md))))
                 <= total (map zpair (vm_maps (m_vmmaps md)))).
    { apply total_filter_le. intros e He. apply in_map_iff in He as (e' & <- & He').
      destruct (Hent e' ltac:(apply in_app_iff; right; exact He')) as (_ & [Hp _] & _). exact Hp. }
    pose proof (filter_length_le (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized md)) as Hlen.
    apply Nat2Z.inj_le in Hlen. unfold PGSZ in *. nia.
Qed.
