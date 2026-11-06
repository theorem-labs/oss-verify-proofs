(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "odefault"; "cell"; "sstate"; "valuation"; "soff"; "ob_hi"; "ob_lo"; "obj_holds"; "obj_range"; "mkObj"; "ob_cells"; "ob_dflt"; "ranges_disjoint"; "eval"; "is_arr"; "ob_base"; "smatch"; "c_off"; "obj_wf"; "sprop"; "DUnknown"; "c_width"; "ss_objs"; "DList"; "DRom"; "SAlu"; "SLit"; "obj_hi_of"; "obj_lo_of"; "ss_facts"; "sv_below"; "DImage"; "DZero"; "dflt_holds"; "holds"; "mem_match"; "outside_all"; "rom_ok"; "ss_next"; "swf"; "tfact"; "SAluW"; "SExt"; "SLBytes"; "SMd"; "SMdW"; "SVar"; "c_val"; "mkCell"; "sv_eqb"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "iff"; "or"; "@Corelib.Init.Datatypes"; "bool"; "option"; "prod"; "Some"; "app"; "list"; "true"; "cons"; "false"; "andb"; "None"; "pair"; "fst"; "snd"; "S"; "nat"; "negb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "leb"; "modulo"; "sub"; "ltb"; "opp"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "snorm"; "same_atoms"; "set_objs"; "itv"; "mk_addk"; "sitv"; "in_bounds"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM"; "pdr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.Rebase"; "shift_off"; "shift_ok"; "rebase_obj"; "shift_cell"; "rebase_obj_at"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.WithSegs"; "in_range"; "dflt_merge"; "obj_merge"; "sub_range"; "merge_objs_at"; "split_obj_at"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "map"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "obj_split"; "part_cells"; "cell_side"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV"; "U"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma soff_snorm : ltac2:(tb__ "0|0|
S8S4S37S0S9R2R1A2S58S7dR2R1A2A1A3Fe;Frho;").
Proof.
  intros rho e. unfold soff, U, bv_signed, bv_swrap, bv_wrap, snorm.
  change (bv_half_modulus 64) with (2 ^ 63). rewrite two64.
  pose proof (urange (eval rho e)) as R. set (u := bv_unsigned (eval rho e)) in *.
  rewrite (Z.mod_small u) by lia.
  destruct (Z.ltb_spec u (2 ^ 63)).
  - rewrite Z.mod_small by lia. lia.
  - replace (u + 2 ^ 63) with ((u - 2 ^ 63) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma snorm_small : ltac2:(tb__ "0|1|
S0S38S4eS56S50Z2Z3fA2M0A1R1A2S51R1G0A2A2S37S0S58R2A1R2A3F_;Fz;").
Proof.
  intros z Hz. unfold snorm.
  destruct (Z_lt_ge_dec z 0).
  - rewrite <- (Z.mod_add z 1 (2 ^ 64)) by lia. rewrite (Z.mod_small (z + 1 * 2 ^ 64)) by lia.
    destruct (Z.ltb_spec (z + 1 * 2 ^ 64) (2 ^ 63)); lia.
  - rewrite (Z.mod_small z) by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia.
Qed.

Lemma mod_eq_multiple : ltac2:(tb__ "0|0|
S0S0S0S51Z0R1A2S37S0S53R4R2A2S53R3R2A2A3S3aS0S0S37S0S54R6R5A2S57R4R1A2A3Lq;A2F_;F_;Fm;Fb;Fa;").
Proof.
  intros a b m Hm H.
  pose proof (Z.div_mod a m ltac:(lia)) as Da. pose proof (Z.div_mod b m ltac:(lia)) as Db.
  exists (a / m - b / m). nia.
Qed.

Lemma soff_diff_lit : ltac2:(tb__ "0|2|
S8S4S4S0S0S0S37S3eS0A1S59R5R4A2S40S0R3A2A3S38S4eR3S9R7R6A2M0A2S4eG0R2A2A2S38S4eR4S9R8R6A2M1A2S4eG1R3A2A2S51S54R4R5A2S50Z2Z3fA2A2S37S0S9RaR9A2S4fS9RaR8A2S58R7A1A2A3F_;F_;F_;F_;Fhi;Flo;Fd0;Fx;Fa;Frho;").
Proof.
  intros rho a x d0 lo hi Hs Ha Hx Hw.
  pose proof (same_atoms_sound rho a x d0 Hs) as E.
  rewrite !soff_snorm in *.
  pose proof (U_range rho a) as Ra. pose proof (U_range rho x) as Rx.
  set (ua := U rho a) in *. set (ux := U rho x) in *.
  assert (SN : forall u, 0 <= u < 2 ^ 64 -> snorm u = u \/ snorm u = u - 2 ^ 64).
  { intros u Hu. unfold snorm. rewrite Z.mod_small by lia. destruct (u <? 2 ^ 63); lia. }
  pose proof (snorm_range d0) as Rd.
  assert (E1 : exists q, (ux + d0) - ua = 2 ^ 64 * q).
  { apply mod_eq_multiple; [lia|]. rewrite E. rewrite Z.mod_mod by lia. reflexivity. }
  assert (E2 : exists q, d0 - snorm d0 = 2 ^ 64 * q).
  { apply mod_eq_multiple; [lia|]. symmetry. apply snorm_mod. }
  destruct E1 as [q1 H1]. destruct E2 as [q2 H2].
  destruct (SN ua Ra) as [Sa|Sa]; destruct (SN ux Rx) as [Sx|Sx]; rewrite Sa, Sx in *; nia.
Qed.

Lemma same_atoms_eq : ltac2:(tb__ "0|0|
S8S4S4S37S3eS0A1S59R2R1A2S40S0Z0A2A3S37S72Q40A1S12R4R3A2S12R4R2A2A3F_;Fx;Fa;Frho;").
Proof.
  intros rho a x H. pose proof (same_atoms_sound rho a x 0 H) as E.
  rewrite Z.add_0_r in E. unfold U in E. pose proof (urange (eval rho x)).
  rewrite Z.mod_small in E by lia. apply bv_eq. exact E.
Qed.

Definition cell_side (c : cell) (mid : sv) : option bool := ltac2:(tb__ "0|4|
S3eS0A1S3eS3dA1M0Lx;S59S16Vc;A1Vmid;A2S0S58R1A1S0S3dG0L_;M1S52S4fR1S1aVc;A1A2Z0M2A2S40S3dS43A2G1S52G2R1A2S40S3dS45A2S47S3dA1M3X3dx2X3dx2Td;Ld;G3X3ex2").

Fixpoint part_cells (cells : list cell) (mid : sv) : option (list cell * list cell) :=
  match cells with
  | [] => Some ([], [])
  | c :: rest =>
      match cell_side c mid, part_cells rest mid with
      | Some true, Some (l, r) => Some (c :: l, r)
      | Some false, Some (l, r) => Some (l, c :: r)
      | _, _ => None
      end
  end.

Definition obj_split (o : sobj) (mid : sv) : option (sobj * sobj) := ltac2:(tb__ "0|8|
S5S3eS3fS3S3A2M0A1M1Lx;S10Vo;A1S19S5S3eS3fS42S6A1M2G2A2M3A1G1Lx;S7bSfVo;A1Vmid;A2G3G3G1Lp;R1G2G2S40G0S48S3S3SeS14Vo;A1M4SbVo;A1Vmid;R2R4A5SeG4Vmid;SaVo;A1R1R4A5A4A2Lrc;Llc;X3fx1Lp;S47G0A1M5X3ex2M6Td;S25S5G6Td;S24S5G6Td;S1G5Ll;M7G7S0S4S42S3fS0S0A2A1S42S2dA1G5Ltmpl;Lflds;Lcnt;Lesz;X5x6").

Lemma part_cells_spec : ltac2:(tb__ "0|5|
S42S6A1M0S4G0G0S37S3eS3fG0G0A2M1A1S7bR4R3A2S40G1S48G0G0R2R1A4A2A3S38S6S5fS6R1R4A3S38S5fS6R2R7A3M2S37S3eS3dA1M3S7cR2R6A2M4S40S3dS43A2A3A2F_;Fc;S38S6S5fS6R1R3A3S38G2S37G3G4S40S3dS45A2A3A2F_;Fc;S6S5fS6R1R6A3S3cS5fS6R2R5A3S5fS6R2R4A3A2F_;Fc;A2A2F_;Fr;Fl;Fmid;Fcells;").
Proof.
  induction cells as [|c rest IH]; intros mid l r H; cbn in H.
  - inversion H; subst. split; [|split]; intros c0 Hin; cbn in Hin; tauto.
  - destruct (cell_side c mid) as [[|]|] eqn:Es; [| |discriminate];
    destruct (part_cells rest mid) as [[l' r']|] eqn:Ep; try discriminate; injection H as <- <-;
    destruct (IH mid l' r' Ep) as (A & B & C); (split; [|split]); intros c' Hin'; cbn in Hin' |- *.
    + destruct Hin' as [<-|Hin']; [auto|]. destruct (A c' Hin'); auto.
    + destruct (B c' Hin'); auto.
    + destruct Hin' as [<-|Hin']; [auto|]. destruct (C c' Hin'); auto.
    + destruct (A c' Hin'); auto.
    + destruct Hin' as [<-|Hin']; [auto|]. destruct (B c' Hin'); auto.
    + destruct Hin' as [<-|Hin']; [auto|]. destruct (C c' Hin'); auto.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma cell_side_sound : ltac2:(tb__ "0|3|
S8S71S3S6S4S3dScVsegs;R6R5R4A4S5fS6R4SfR5A1A3S4eZ0S1aR5A1A2S38S4eS21R9R7A2S9R9R5A2M0A2S4eG0S20R9R7A2A2A2S37S3eS3dA1S7cR7R6A2S40S3dR5A2A3S3dOLsd;R6S4eS4fS9RbS16R8A1A2M1S1aR8A1A2S9RbR7A2M2A2S4eG2G1A2X3dx2F_;F_;F_;F_;F_;Fsd;Fmid;Fc;Fo;Fms;Frho;").
Proof using .
  intros rho ms o c mid sd Ho Hin Hw0 Hmid Hs.
  destruct Ho as (Hrng & _ & Hcells & _ & _).
  pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (Hlo & Hhi & _).
  unfold cell_side in Hs. destruct (same_atoms (c_off c) mid) as [d|] eqn:E; [|discriminate].
  pose proof (soff_diff_lit rho (c_off c) mid d (obj_lo_of rho o) (obj_hi_of rho o) E) as D.
  assert (W : 0 <= c_width c \/ c_width c < 0) by lia.
  cbn zeta in Hs.
  destruct (Z.leb_spec (snorm d + c_width c) 0).
  - inversion Hs; subst. cbn. specialize (D ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  - destruct (Z.leb_spec 0 (snorm d)); [|discriminate]. inversion Hs; subst. cbn.
    specialize (D ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma obj_split_shape : ltac2:(tb__ "0|6|
S3S4S3S3S37S3eS3fS3S3A2M0A1S7aR4R3A2S40G0S48S3S3R2R1A4A2A3S3aS42S6A1M1G1S3aG1G1S38S37S3R5SeS14R7A1M2SbR7A1R6R2S10R7A1M3A5A3S38S37S3R4SeG2R6SaR7A1R1G3A5A3S38S37S3eS3fG1G1A2M4A1S7bSfR7A1R6A2S40G4S48G1G1R2R1A4A2A3S38S1S39S37S5S10R8A1M5S1cR1A1A3A1Fl;S38S1S39S37S5G5S1dR1A1A3A1Fl;S37S3dS13G3A1S45A3A2A2A2A2A2Lrc;A2Llc;A2F_;Fo2;Fo1;Fmid;Fo;").
Proof using .
  intros o mid o1 o2 Hsp. unfold obj_split in Hsp.
  assert (NL : forall l, ob_dflt o <> DList l).
  { intros l E. rewrite E in Hsp. discriminate. }
  assert (NR : forall l, ob_dflt o <> DRom l).
  { intros l E. rewrite E in Hsp. discriminate. }
  assert (NA : is_arr (ob_dflt o) = false).
  { destruct (ob_dflt o); try reflexivity. discriminate. }
  assert (ND : match part_cells (ob_cells o) mid with
          | Some (lc, rc) => Some (mkObj (ob_base o) (ob_lo o) mid lc (ob_dflt o), mkObj (ob_base o) mid (ob_hi o) rc (ob_dflt o))
          | None => None end = Some (o1, o2)).
  { destruct (ob_dflt o); try exact Hsp; try discriminate NA; exfalso; [exact (NL _ eq_refl) | exact (NR _ eq_refl)]. }
  clear Hsp. destruct (part_cells (ob_cells o) mid) as [[lc rc]|] eqn:Ep; [|discriminate].
  injection ND as <- <-. exists lc, rc. repeat split; auto.
Qed.

Lemma obj_split_holds : ltac2:(tb__ "0|2|
S8S71S3S4S3S3S1S37S3eS3fS3S3A2M0A1S7aR5R4A2S40G0S48S3S3R3R2A4A2A3S37S3dS17R2R6A2S43A3ScVsegs;R9R8R7A4S38S4eS21RaR8A2S9RaR7A2M1A2S4eG1S20RaR8A2A2A2S38ScVsegs;RbRaR7A4ScVsegs;RbRaR6A4A2F_;F_;F_;F_;Fn;Fo2;Fo1;Fmid;Fo;Fms;Frho;").
Proof using .
  intros rho ms o mid o1 o2 n Hsp Hwf Ho Hmid.
  assert (CW : forall c, In c (ob_cells o) -> 0 <= c_width c).
  { intros c Hc. unfold obj_wf in Hwf. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [_ Hwf].
    pose proof (proj1 (forallb_forall _ _) Hwf c Hc) as W. unfold cell_wf in W.
    repeat (apply andb_prop in W as [W ?]). apply Z.ltb_lt in W. lia. }
  destruct (obj_split_shape o mid o1 o2 Hsp) as (lc & rc & -> & -> & Ep & NL & NR & NA).
  pose proof (part_cells_spec _ _ _ _ Ep) as (PL & PR & PC).
  assert (SL : forall c, In c lc -> soff rho (c_off c) + c_width c <= soff rho mid).
  { intros c Hc. destruct (PL c Hc) as [Hin Hs].
    exact (cell_side_sound rho ms o c mid true Ho Hin (CW c Hin) Hmid Hs). }
  assert (SR : forall c, In c rc -> soff rho mid <= soff rho (c_off c)).
  { intros c Hc. destruct (PR c Hc) as [Hin Hs].
    exact (cell_side_sound rho ms o c mid false Ho Hin (CW c Hin) Hmid Hs). }
  destruct Ho as (Hrng & Hwr & Hcells & Hdf & Hlen).
  unfold obj_lo_of, obj_hi_of in *.
  unfold obj_holds; cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]; unfold obj_lo_of, obj_hi_of; cbn [ob_lo ob_hi].
  set (b := bv_unsigned (eval rho (ob_base o))) in *.
  set (lo := soff rho (ob_lo o)) in *. set (hi := soff rho (ob_hi o)) in *.
  set (m := soff rho mid) in *.
  assert (DF : forall off, lo <= off < hi -> ~ covered rho (ob_cells o) off ->
               dflt_holds segs rho (ob_dflt o) lo off ms (Z_to_bv 64 (b + off))) by exact Hdf.
  split.
  -
    split; [lia|]. split; [intros off Hoff Hdw; apply Hwr; [lia | exact Hdw]|].
    split.
    { apply Forall_forall. intros c Hc. destruct (PL c Hc) as [Hin _].
      pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (A & B & C).
      pose proof (SL c Hc). split; [exact A|]. split; [lia|]. exact C. }
    split.
    { intros off Hoff Hnc. apply DF; [lia|]. intros Hcov. apply Hnc.
      unfold covered in *. apply Exists_exists in Hcov as (c & Hin & Hic).
      destruct (PC c Hin) as [Hl|Hr].
      - apply Exists_exists. exists c. auto.
      - exfalso. pose proof (SR c Hr). unfold in_cell in Hic. lia. }
    destruct (ob_dflt o); cbn; try exact I; try discriminate NA; exfalso; [exact (NL _ eq_refl) | exact (NR _ eq_refl)].
  -
    split; [lia|]. split; [intros off Hoff Hdw; apply Hwr; [lia | exact Hdw]|].
    split.
    { apply Forall_forall. intros c Hc. destruct (PR c Hc) as [Hin _].
      pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (A & B & C).
      pose proof (SR c Hc). split; [lia|]. split; [exact B|]. exact C. }
    split.
    { intros off Hoff Hnc.
      assert (Hd : dflt_holds segs rho (ob_dflt o) lo off ms (Z_to_bv 64 (b + off))).
      { apply DF; [lia|]. intros Hcov. apply Hnc.
        unfold covered in *. apply Exists_exists in Hcov as (c & Hin & Hic).
        destruct (PC c Hin) as [Hl|Hr].
        - exfalso. pose proof (SL c Hl). unfold in_cell in Hic. lia.
        - apply Exists_exists. exists c. auto. }
      destruct (ob_dflt o); cbn in *; try exact Hd; exfalso; [exact (NL _ eq_refl) | exact (NR _ eq_refl)]. }
    destruct (ob_dflt o); cbn; try exact I; try discriminate NA; exfalso; [exact (NL _ eq_refl) | exact (NR _ eq_refl)].
Qed.

Definition in_range (r : Z * Z) (a : Z) : Prop := ltac2:(tb__ "0|0|
S38S4eS49S0S0Vr;A3Va;A2S51Va;S4aS0S0Vr;A3A2A2").
Definition sub_range (r1 r : Z * Z) : Prop := ltac2:(tb__ "0|0|
S38S4eS49S0S0Vr;A3S49S0S0Vr1;A3A2S4eS4aS0S0Vr1;A3S4aS0S0Vr;A3A2A2").

Lemma pdr_app_inv : ltac2:(tb__ "0|3|
S42S3fS0S0A2M0A1M1G1S62S41G0R2R1A3A1S38S62R3A1S38S62R2A1G0G0S5fG0R2R5A3M2G2S11R4R3A2F_;F_;Fr2;Fr1;A2A2F_;Fl2;Fl1;").
Proof using .
  induction l1 as [|r t IH]; intros l2 H; cbn in H |- *.
  - repeat split; auto. intros r1 r2 [].
  - destruct H as [Hf Hp]. apply Forall_app in Hf as [Hf1 Hf2]. destruct (IH l2 Hp) as (A & B & C).
    repeat split; auto. intros r1 r2 [<-|Hin] Hin2.
    + exact (proj1 (Forall_forall _ _) Hf2 r2 Hin2).
    + apply C; cbn; auto.
Qed.

Lemma pdr_app : ltac2:(tb__ "0|4|
S42S3fS0S0A2M0A1M1G1S62R2A1M2G2G0G0S5fG0R2R6A3M3G3S11R4R3A2F_;F_;Fr2;Fr1;S62S41G0R5R4A3A1F_;F_;F_;Fl2;Fl1;").
Proof using .
  induction l1 as [|r t IH]; intros l2 H1 H2 Hx; cbn in H1 |- *; [exact H2|].
  destruct H1 as [Hf Hp]. split.
  - apply Forall_app. split; [exact Hf|]. apply Forall_forall. intros r2 Hin. apply Hx; cbn; auto.
  - apply IH; auto. intros r1 r2 Hin1 Hin2. apply Hx; cbn; auto.
Qed.

Lemma ranges_disjoint_sub : ltac2:(tb__ "0|1|
S3fS0S0A2M0G0G0S6eR3R2A2S11R3R2A2S11R5R3A2F_;F_;Fx;Fr;Fr1;").
Proof using . intros [a1 b1] [a b] [u v] [H1 H2] Hd. unfold ranges_disjoint in *. cbn in *. lia. Qed.

Lemma ranges_disjoint_sym : ltac2:(tb__ "0|1|
S3fS0S0A2M0G0S11R2R1A2S11R2R3A2F_;Fx;Fr;").
Proof using . intros [a b] [u v] H. unfold ranges_disjoint in *. cbn in *. lia. Qed.

Lemma pdr_replace2 : ltac2:(tb__ "0|2|
S42S3fS0S0A2M0A1M1G0G1G0G0S62S41G0R5S44G0R4R3A3A3A1S6eR3R5A2S6eR3R6A2S11R5R4A2S62S41G0R9S44G0R6S44G0R5R7A3A3A3A1F_;F_;F_;F_;Fr2;Fr1;Fl2;Fr;Fl1;").
Proof using .
  intros l1 r l2 r1 r2 H S1 S2 D.
  apply pdr_app_inv in H as (P1 & P2 & X). cbn in P2. destruct P2 as [Fr P2].
  apply pdr_app; [exact P1| |].
  - cbn. split; [|split; [|exact P2]].
    + constructor; [exact D|]. apply Forall_forall. intros x Hx.
      eapply ranges_disjoint_sub; [exact S1|]. exact (proj1 (Forall_forall _ _) Fr x Hx).
    + apply Forall_forall. intros x Hx.
      eapply ranges_disjoint_sub; [exact S2|]. exact (proj1 (Forall_forall _ _) Fr x Hx).
  - intros x y Hx Hy. cbn in Hy. destruct Hy as [<-|[<-|Hy]].
    + apply ranges_disjoint_sym. eapply ranges_disjoint_sub; [exact S1|]. apply ranges_disjoint_sym. apply X; cbn; auto.
    + apply ranges_disjoint_sym. eapply ranges_disjoint_sub; [exact S2|]. apply ranges_disjoint_sym. apply X; cbn; auto.
    + apply X; cbn; auto.
Qed.

Lemma pdr_merge2 : ltac2:(tb__ "0|2|
S42S3fS0S0A2M0A1M1G1G0G0G0S62S41G0R5S44G0R3S44G0R2R4A3A3A3A1S0S6bR3R1A2S3cS6bR6R2A2S6bR5R2A2A2F_;Fa;S62S41G0R7S44G0R3R6A3A3A1F_;F_;Fr;Fr2;Fr1;Fl2;Fl1;").
Proof using .
  intros l1 l2 r1 r2 r H Hcov.
  apply pdr_app_inv in H as (P1 & P2 & X). cbn in P2. destruct P2 as [F1 [F2 P2]].
  assert (DJ : forall x, ranges_disjoint r1 x -> ranges_disjoint r2 x -> ranges_disjoint r x).
  { intros [u v] D1 D2. unfold ranges_disjoint, in_range in *. destruct r as [a b], r1 as [a1 b1], r2 as [a2 b2]; cbn in *.
    destruct (Z_lt_ge_dec u v); [|lia]. destruct (Z_lt_ge_dec a b); [|lia].
    destruct (Z_le_gt_dec b u); [lia|]. destruct (Z_le_gt_dec v a); [lia|].
    exfalso.

    assert (exists p, a <= p < b /\ u <= p < v) as (p & Hp & Hq).
    { destruct (Z_le_gt_dec a u); [exists u; lia | exists a; lia]. }
    destruct (Hcov p Hp); lia. }
  apply pdr_app; [exact P1| |].
  - cbn. split; [|exact P2]. apply Forall_forall. intros x Hx. apply Forall_inv_tail in F1.
    apply DJ; [exact (proj1 (Forall_forall _ _) F1 x Hx) | exact (proj1 (Forall_forall _ _) F2 x Hx)].
  - intros x y Hx Hy. cbn in Hy. destruct Hy as [<-|Hy].
    + apply ranges_disjoint_sym. apply DJ; apply ranges_disjoint_sym; apply X; cbn; auto.
    + apply X; cbn; auto.
Qed.

Lemma outside_all_replace : ltac2:(tb__ "0|1|
S8S42S3A1M0S3G0G0S72Q40A1S0S3bS6bSdR7R5A2R1A2S3aS3S3S38S5fS3R1R4A3S6bSdR8R1A2R2A2A2Lo';A2A2Fx;S3bS29R7S41S3R6S44S3R5R4A3A3R2A3S29R7S41S3R6S41S3R3R4A3A3R2A3A2F_;Fa;Fos;Fl2;Fo;Fl1;Frho;").
Proof using .
  intros rho l1 o l2 os a Hcov. unfold outside_all. rewrite !Forall_forall.
  split; intros H x Hin.
  - apply in_app_or in Hin as [Hin|Hin]; [apply H; apply in_or_app; auto|].
    apply in_app_or in Hin as [Hin|Hin]; [|apply H; apply in_or_app; right; cbn; auto].
    cbn zeta. intros Hx. apply (H o ltac:(apply in_or_app; right; cbn; auto)).
    cbn zeta. apply Hcov. exists x. split; [exact Hin|exact Hx].
  - apply in_app_or in Hin as [Hin|Hin]; [apply H; apply in_or_app; auto|].
    cbn in Hin. destruct Hin as [<-|Hin]; [|apply H; apply in_or_app; right; apply in_or_app; auto].
    cbn zeta. intros Hx. apply Hcov in Hx as (o' & Hin' & Hx).
    apply (H o' ltac:(apply in_or_app; right; apply in_or_app; auto)). exact Hx.
Qed.

Lemma mem_match_replace : ltac2:(tb__ "0|1|
S8S71S42S3A1M0S3G0G0S28Vsegs;R6S41S3R4S44S3R3R2A3A3R5A4S74S3ScVsegs;R7R6A3R2A3S62S76S3S3fS0S0A2SdR8A1S41S3R6S41S3R3R4A3A3A4A1S0S3bS6bSdRaR7A2R1A2S3aS3S3S38S5fS3R1R6A3S6bSdRbR1A2R2A2A2Lo';A2A2Fx;S28Vsegs;RaS41S3R8S41S3R5R6A3A3R9A4F_;F_;F_;F_;Fos;Fl2;Fo;Fl1;Fms;Frho;").
Proof using .
  intros rho ms l1 o l2 os (Hall & Hpd & Hfr) Hos Hpdr Hcov.
  split; [|split].
  - apply Forall_app in Hall as [H1 H2]. apply Forall_cons_iff in H2 as [_ H2].
    rewrite !Forall_app. auto.
  - apply pairwise_disjoint_pdr. exact Hpdr.
  - intros a Ha. apply Hfr. apply (outside_all_replace rho l1 o l2 os a Hcov). exact Ha.
Qed.

Definition split_obj_at (S : sstate) (i : nat) (mid : sv) : option sstate := ltac2:(tb__ "0|4|
S3eS3A1S3eS7A1M0Lx;S60S3S1bVS;A1M1Vi;A3S3S3dG0L_;S46S23S2bVS;A1Vmid;A2S5eS22VS;A1SbR1A1SaR1A1Vmid;Z0A5A2S3eS3fS3S3A2M2A1G0Lx;S7aR1Vmid;A2G2G2G0Lp;R1S3S3S40S7S5aVS;S41S3S75S3Vi;G1A3S44S3R2S44S3R1S77S3S4bVi;A1G1A3A3A3A3A2A2Lo2;Lo1;X3fx1Lp;S47S7A1M3X3ex2G3X3dx2Lo;G3X3ex2").

Lemma nth_error_split3 : forall {A} (l : list A) i x,
  nth_error l i = Some x -> l = firstn i l ++ x :: skipn (Datatypes.S i) l.
Proof using .
  intros A l. induction l as [|h t IH]; intros i x H; destruct i; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - f_equal. apply IH. exact H.
Qed.

Lemma swf_objs_replace : ltac2:(tb__ "0|1|
S7S42S3A1M0S3G0G0S37S3dS2cR5A1S43A3S37G0S1bR6A1S41S3R5S44S3R4R3A3A3A3S37S3dS61S3S17S2bR7A1A1R3A3S43A3S37S3dS2cS5aR8S41S3R7S41S3R4R5A3A3A2A1S43A3F_;F_;F_;Fos;Fl2;Fo;Fl1;FS;").
Proof using .
  intros S l1 o l2 os Hwf Ho Hos. unfold swf in *. cbn [set_objs ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in *.
  rewrite Ho in Hwf. repeat (apply andb_prop in Hwf; destruct Hwf as [Hwf ?]).
  rewrite forallb_app in H0. cbn in H0. apply andb_prop in H0 as [A B]. apply andb_prop in B as [B C].
  repeat (apply andb_true_intro; split); try assumption.
  rewrite !forallb_app. rewrite A, Hos, C. reflexivity.
Qed.

Theorem smatch_split : ltac2:(tb__ "0|0|
S8S7S4cS4S7S3fS42S79A1S78A2S37S3eS7A1S70R5R4R3A3S40S7R2A2A3S15Vsegs;R7R6R2A4S15Vsegs;R8R4R3A4F_;F_;Fw;FS';Fmid;Fi;FS;Frho;").
Proof using .
  intros rho S i mid S' [tr [ms md]] Hsp Hsm.
  unfold split_obj_at in Hsp.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hn; [|discriminate].
  destruct (sv_below (ss_next S) mid && in_bounds (ss_facts S) (ob_lo o) (ob_hi o) mid 0)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hb Hib].
  destruct (obj_split o mid) as [[o1 o2]|] eqn:Ho; [|discriminate]. injection Hsp as <-.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 _ _ _ Hn) as EQ.
  assert (Hwfo : obj_wf (ss_next S) o = true).
  { pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [_ W]. apply andb_prop in W as [W _]. exact W. }
  assert (Hoh : obj_holds segs rho ms o).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall]. inversion Hall; auto. }
  pose proof (in_bounds_sound rho (ss_facts S) (ob_lo o) (ob_hi o) mid 0 Hfacts ltac:(lia) Hib) as [M1 M2].
  destruct (obj_split_holds rho ms o mid o1 o2 (ss_next S) Ho Hwfo Hoh ltac:(unfold obj_lo_of, obj_hi_of; lia)) as [H1 H2].
  destruct (obj_split_shape o mid o1 o2 Ho) as (lc & rc & E1 & E2 & Ep & NL & NR & NA).
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { change (firstn i (ss_objs S) ++ o1 :: o2 :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o1; o2] ++ skipn (Datatypes.S i) (ss_objs S)).
    eapply swf_objs_replace; [exact Hwf | exact EQ |].
    subst o1 o2. unfold obj_wf in Hwfo |- *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb].
    repeat (apply andb_prop in Hwfo; destruct Hwfo as [Hwfo ?]).
    pose proof (part_cells_spec _ _ _ _ Ep) as (PL & PR & _).
    assert (FL : forallb (cell_wf (ss_next S)) lc = true).
    { apply forallb_forall. intros c Hc. apply (proj1 (forallb_forall _ _) H0). apply PL. exact Hc. }
    assert (FR : forallb (cell_wf (ss_next S)) rc = true).
    { apply forallb_forall. intros c Hc. apply (proj1 (forallb_forall _ _) H0). apply PR. exact Hc. }
    rewrite Hwfo, H4, Hb, H3, FL, FR, H. reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  change (firstn i (ss_objs S) ++ o1 :: o2 :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o1; o2] ++ skipn (Datatypes.S i) (ss_objs S)).
  assert (R1 : obj_range rho o1 = (fst (obj_range rho o), fst (obj_range rho o) - obj_lo_of rho o + soff rho mid)).
  { subst o1. unfold obj_range, obj_lo_of, obj_hi_of. cbn. f_equal. lia. }
  assert (R2 : obj_range rho o2 = (fst (obj_range rho o) - obj_lo_of rho o + soff rho mid, snd (obj_range rho o))).
  { subst o2. unfold obj_range, obj_lo_of, obj_hi_of. cbn. f_equal; lia. }
  apply mem_match_replace with (o := o).
  - exact Hmem.
  - constructor; [exact H1|]. constructor; [exact H2|]. constructor.
  - destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *.
    eapply pdr_replace2; [exact Hpd | | |];
      rewrite ?R1, ?R2; unfold sub_range, ranges_disjoint, obj_range, obj_lo_of, obj_hi_of in *; cbn in *; lia.
  - intros x. split.
    + intros Hx. destruct (Z_lt_ge_dec x (fst (obj_range rho o) - obj_lo_of rho o + soff rho mid)).
      * exists o1. split; [cbn; auto|]. rewrite R1. revert Hx l M1 M2. clear.
        unfold in_range, obj_range, obj_lo_of, obj_hi_of. cbn [fst snd]. intros; lia.
      * exists o2. split; [cbn; auto|]. rewrite R2. revert Hx g M1 M2. clear.
        unfold in_range, obj_range, obj_lo_of, obj_hi_of. cbn [fst snd]. intros; lia.
    + intros (o' & Hin' & Hx). destruct Hin' as [<-|[<-|[]]]; [rewrite R1 in Hx|rewrite R2 in Hx];
        revert Hx M1 M2; clear; unfold in_range, obj_range, obj_lo_of, obj_hi_of; cbn [fst snd]; intros; lia.
Qed.

Definition dflt_merge (d1 d2 : odefault) : option odefault := ltac2:(tb__ "0|9|
S5S3eS5A1M0Ld1;Vd1;S5G0Ld2;M1Vd2;S40S5S19A2M2G2G2S1S47S5A1M3Ll;M4G4S0S4S42S3fS0S0A2A1M5S42S2dA1M6G3Ltmpl;Lflds;Lcnt;Lesz;M7X5x6G1Vd2;G2S40S5S25A2G2G4G4G7X5x6G1Vd2;G2G2S40S5S24A2G4G4G7X5x6G4S1G1Vd2;G3G3G3S1G3Ll0;M8G8G7X5x6Ll;S0S4G5G6G1Vd2;G3G3G3G4G4S0S4G5G6G3Ltmpl0;Lflds0;Lcnt0;Lesz0;X5x6Ltmpl;Lflds;Lcnt;Lesz;X5x6").

Definition obj_merge (o1 o2 : sobj) : option sobj := ltac2:(tb__ "0|4|
S3dS3eS3A1M0L_;S46S36S14Vo1;A1M1S14Vo2;A1A2S3eS0A1S3dLx;S59SaVo1;A1SbVo2;A1A2S0S0S3dLz;R1S43S1S45Lp;M2G2X0x3Lz;S45X3ex2A2S3eS5A1G0Lx;S6cS10Vo1;A1S10Vo2;A1A2S5S40S3SeG1SbVo1;A1SaVo2;A1S41S6SfVo1;A1SfVo2;A1A3R1A5A2Ld;S47S3A1M3X3ex2G3X3dx2").

Lemma dflt_holds_weaken : ltac2:(tb__ "0|0|
S8S5S0S0S71S72Q40A1S2aVsegs;R2A2S1S39S37S5R7S1cR1A1A3A1Fl;S1S39S37S5R8S1dR1A1A3A1Fl;S26Vsegs;R9R8R7R6R5R4A7S26Vsegs;RaS19R8R7R6R5A7F_;F_;F_;F_;Fa;Fms;Foff;Flo;Fd;Frho;").
Proof using .
  intros rho d lo off ms a Hrom Hnl Hnr Hd. destruct d; cbn in *.
  - exact Hd.
  - eexists; exact Hd.
  - destruct Hd as [Hn [b Hb]]. exists b. rewrite (rd_rom segs ms a Hrom Hn). exact Hb.
  - exfalso. exact (Hnl _ eq_refl).
  - exfalso. exact (Hnr _ eq_refl).
  - exact Hd.
Qed.

Lemma dflt_merge_spec : ltac2:(tb__ "0|2|
S5S5S5S37S3eS5A1S6cR3R2A2S40S5R1A2A3S38S1S39S37S5R5S1cR1A1M0A3A1Fl;S38S1S39S37S5R4G0A3A1Fl;S38S1S39S37S5R5S1dR1A1M1A3A1Fl;S38S1S39S37S5R4G1A3A1Fl;S3cS38S37S5R2R4A3S37S5R2R3A3A2S37S5R2S19A3A2A2A2A2A2F_;Fd;Fd2;Fd1;").
Proof using .
  intros d1 d2 d H. destruct d1, d2; cbn in H; inversion H; subst;
    (split; [intros l; discriminate|]); (split; [intros l; discriminate|]);
    (split; [intros l; discriminate|]); (split; [intros l; discriminate|]); auto.
Qed.

Lemma dflt_merge_noarr : ltac2:(tb__ "0|0|
S5S5S5S37S3eS5A1S6cR3R2A2S40S5R1A2A3S38S37S3dS13R4A1S45A3S38S37S3dS13R3A1S45A3S37S3dS13R2A1S45A3A2A2F_;Fd;Fd2;Fd1;").
Proof using . intros d1 d2 d H. destruct d1, d2; cbn in H; inversion H; subst; cbn; auto. Qed.

Lemma obj_merge_holds : ltac2:(tb__ "0|2|
S8S71S3S3S3S2aVsegs;R4A2S37S3eS3A1S6dR4R3A2S40S3R2A2A3ScVsegs;R7R6R5A4ScVsegs;R8R7R5A4S51S54S20R9R6A2S21R9R7A2A2S50Z2Z3fA2A2S38ScVsegs;RaR9R6A4S38S37S3fS0S0A2SdRaR6A2S48S0S0S49S0S0SdRaR8A2M0A3S4aS0S0SdRaR7A2M1A3A4A3S37S0S4aS0S0G0A3S49S0S0G1A3A3A2A2F_;F_;F_;F_;F_;Fo;Fo2;Fo1;Fms;Frho;").
Proof using .
  intros rho ms o1 o2 o Hrom Hm H1 H2 Hw.
  unfold obj_merge in Hm.
  destruct (sv_eqb (ob_base o1) (ob_base o2)) eqn:Eb; [|discriminate].
  destruct (same_atoms (ob_hi o1) (ob_lo o2)) as [[|p|p]|] eqn:Ea; try discriminate. cbn in Hm.
  destruct (dflt_merge (ob_dflt o1) (ob_dflt o2)) as [d|] eqn:Ed; [|discriminate]. injection Hm as <-.
  apply sv_eqb_sound in Eb.
  pose proof (same_atoms_eq rho _ _ Ea) as Eq.
  assert (ADJ : obj_hi_of rho o1 = obj_lo_of rho o2).
  { unfold obj_hi_of, obj_lo_of, soff. rewrite Eq. reflexivity. }
  destruct (dflt_merge_spec _ _ _ Ed) as (NL1 & NL2 & NR1 & NR2 & Dd).
  destruct (dflt_merge_noarr _ _ _ Ed) as (NA1 & NA2 & NAd).
  destruct H1 as (R1 & W1 & C1 & D1 & L1). destruct H2 as (R2 & W2 & C2 & D2 & L2).
  rewrite <- Eb in *.
  unfold obj_holds, obj_range. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  unfold obj_lo_of, obj_hi_of in *. cbn [ob_lo ob_hi] in *.
  set (b := bv_unsigned (eval rho (ob_base o1))) in *.
  set (lo1 := soff rho (ob_lo o1)) in *. set (hi1 := soff rho (ob_hi o1)) in *.
  set (lo2 := soff rho (ob_lo o2)) in *. set (hi2 := soff rho (ob_hi o2)) in *.
  split; [|split; [cbn [fst snd]; rewrite <- Eb; reflexivity | cbn [fst snd]; rewrite <- Eb; subst b lo1 hi1 lo2 hi2; lia]].
  split; [lia|].
  split. { intros off Hoff Hdw.
           assert (D1w : dflt_writable (ob_dflt o1) = true) by (destruct (ob_dflt o1); try reflexivity; exfalso; exact (NR1 _ eq_refl)).
           assert (D2w : dflt_writable (ob_dflt o2) = true) by (destruct (ob_dflt o2); try reflexivity; exfalso; exact (NR2 _ eq_refl)).
           destruct (Z_lt_ge_dec off hi1); [apply W1; [lia|exact D1w] | apply W2; [lia|exact D2w]]. }
  split.
  { apply Forall_app. split.
    - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) C1 c Hc) as (A & B & C). repeat split; try lia. exact C.
    - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) C2 c Hc) as (A & B & C). repeat split; try lia. exact C. }
  split.
  { intros off Hoff Hnc.
    assert (NC1 : ~ covered rho (ob_cells o1) off).
    { intros H. apply Hnc. unfold covered in *. apply Exists_exists in H as (c & Hin & Hic). apply Exists_exists. exists c. split; [apply in_or_app; auto|exact Hic]. }
    assert (NC2 : ~ covered rho (ob_cells o2) off).
    { intros H. apply Hnc. unfold covered in *. apply Exists_exists in H as (c & Hin & Hic). apply Exists_exists. exists c. split; [apply in_or_app; auto|exact Hic]. }
    destruct (Z_lt_ge_dec off hi1).
    - specialize (D1 off ltac:(lia) NC1).
      destruct Dd as [[-> _]| ->]; [exact D1|]. apply (dflt_holds_weaken rho (ob_dflt o1)); [exact Hrom | exact NL1 | exact NR1 | exact D1].
    - specialize (D2 off ltac:(lia) NC2).
      destruct Dd as [[_ ->]| ->].
      +
        destruct (ob_dflt o2); cbn in *; try exact D2; exfalso; [exact (NL2 _ eq_refl) | exact (NR2 _ eq_refl)].
      + apply (dflt_holds_weaken rho (ob_dflt o2)); [exact Hrom | exact NL2 | exact NR2 |].
        destruct (ob_dflt o2); cbn in *; try exact D2; try discriminate NA2; exfalso; [exact (NL2 _ eq_refl) | exact (NR2 _ eq_refl)]. }
  destruct Dd as [[E1 E2]| ->]; cbn; [|exact I].
  destruct d; cbn; try exact I; try discriminate NAd; exfalso; [exact (NL1 _ (eq_sym E1)) | exact (NR1 _ (eq_sym E1))].
Qed.

Lemma obj_wf_merge : ltac2:(tb__ "0|0|
S1S3S3S3S37S3eS3A1S6dR3R2A2S40S3R1A2A3S37S3dS17R5R4A2S43A3S37S3dS17R6R4A2S43A3S37S3dS17R7R4A2S43A3F_;F_;F_;Fo;Fo2;Fo1;Fn;").
Proof using .
  intros n o1 o2 o Hm W1 W2. unfold obj_merge in Hm.
  destruct (_ && _)%bool; [|discriminate].
  destruct (dflt_merge (ob_dflt o1) (ob_dflt o2)) as [d|] eqn:Ed; [|discriminate]. injection Hm as <-.
  destruct (dflt_merge_noarr _ _ _ Ed) as (_ & _ & NAd).
  unfold obj_wf in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  apply andb_prop in W1 as [W1 D1]. apply andb_prop in W1 as [W1 C1]. apply andb_prop in W1 as [W1 H1]. apply andb_prop in W1 as [B1 L1].
  apply andb_prop in W2 as [W2 D2]. apply andb_prop in W2 as [W2 C2]. apply andb_prop in W2 as [W2 H2]. apply andb_prop in W2 as [B2 L2].
  rewrite forallb_app, B1, L1, H2, C1, C2. destruct d; try reflexivity. discriminate NAd.
Qed.

Definition merge_objs_at (S : sstate) (i : nat) : option sstate := ltac2:(tb__ "0|8|
S3eS3A1S3eS7A1M0Lx;M1S60S3S1bVS;A1M2Vi;A3S3G1S60S3G2S4bVi;A1M3A3S3S3eS3fS0S0A2M4A1G0Lx;M5S5dS22VS;A1M6SbR2A1A2G4G4G0Lp;R1S0S0G5S5dG6SaR4A1A2G4G4G0Lp0;R1S0S0S3dG0L_;S55S54R1R5A2S50Z2Z3fA2A2G1S6dR8R7A2S3S40S7S5aVS;S41S3S75S3Vi;G2A3S44S3R1S77S3S4bG3A1G2A3A3A3A2A2Lo;S47S7A1M7X3ex2G7X3dx2Lh2;Lz0;X3fx1Lp0;G7X3ex2Lz;Ll1;X3fx1Lp;G7X3ex2Lo2;G7X3ex2Lo1;G7X3ex2").

Lemma nth_error_split4 : forall {A} (l : list A) i x y,
  nth_error l i = Some x -> nth_error l (Datatypes.S i) = Some y ->
  l = firstn i l ++ x :: y :: skipn (Datatypes.S (Datatypes.S i)) l.
Proof using .
  intros A l. induction l as [|h t IH]; intros i x y Hx Hy; destruct i; cbn in *; try discriminate.
  - injection Hx as ->. destruct t; cbn in *; [discriminate|]. injection Hy as ->. reflexivity.
  - f_equal. apply IH; assumption.
Qed.

Theorem smatch_merge : ltac2:(tb__ "0|0|
S8S7S4cS7S3fS42S79A1S78A2S37S3eS7A1S6fR4R3A2S40S7R2A2A3S15Vsegs;R6R5R2A4S15Vsegs;R7R4R3A4F_;F_;Fw;FS';Fi;FS;Frho;").
Proof using .
  intros rho S i S' [tr [ms md]] Hmg Hsm.
  unfold merge_objs_at in Hmg.
  destruct (nth_error (ss_objs S) i) as [o1|] eqn:Hn1; [|discriminate].
  destruct (nth_error (ss_objs S) (Datatypes.S i)) as [o2|] eqn:Hn2; [|discriminate].
  destruct (sitv (ss_facts S) (ob_lo o1)) as [[l1 h1]|] eqn:Hs1; [|discriminate].
  destruct (sitv (ss_facts S) (ob_hi o2)) as [[l2 h2]|] eqn:Hs2; [|discriminate].
  destruct (Z.ltb_spec (h2 - l1) (2 ^ 63)) as [Hlt|]; [|discriminate].
  destruct (obj_merge o1 o2) as [o|] eqn:Ho; [|discriminate]. injection Hmg as <-.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split4 _ _ _ _ Hn1 Hn2) as EQ.
  assert (Ho1 : obj_holds segs rho ms o1 /\ obj_holds segs rho ms o2).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall].
    inversion Hall as [|? ? A B]; subst. inversion B; subst. auto. }
  destruct Ho1 as [Ho1 Ho2].
  pose proof (sitv_sound rho (ss_facts S) (ob_lo o1) l1 h1 Hfacts Hs1) as (B1 & _).
  pose proof (sitv_sound rho (ss_facts S) (ob_hi o2) l2 h2 Hfacts Hs2) as (B2 & _).
  destruct (obj_merge_holds rho ms o1 o2 o Hrom Ho Ho1 Ho2 ltac:(unfold obj_lo_of, obj_hi_of; lia)) as (Hoh & Rng & Adj).
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { change (firstn i (ss_objs S) ++ o :: skipn (Datatypes.S (Datatypes.S i)) (ss_objs S))
      with (firstn i (ss_objs S) ++ [o] ++ skipn (Datatypes.S (Datatypes.S i)) (ss_objs S)).
    pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [Wa W]. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 Wb].
    assert (EQ' : ss_objs S = firstn i (ss_objs S) ++ o1 :: ([o2] ++ skipn (Datatypes.S (Datatypes.S i)) (ss_objs S))) by exact EQ.
    pose proof (swf_objs_replace S _ _ _ [] Hwf EQ' eq_refl) as Hwf1. cbn [app] in Hwf1.
    assert (EQ2 : ss_objs (set_objs S (firstn i (ss_objs S) ++ o2 :: skipn (Datatypes.S (Datatypes.S i)) (ss_objs S)))
                  = firstn i (ss_objs S) ++ o2 :: skipn (Datatypes.S (Datatypes.S i)) (ss_objs S)) by reflexivity.
    pose proof (swf_objs_replace _ _ _ _ [o] Hwf1 EQ2) as Hwf2. cbn [app forallb] in Hwf2.
    unfold set_objs in Hwf2. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hwf2.
    apply Hwf2. rewrite (obj_wf_merge _ _ _ _ Ho W1 W2). reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  destruct Hmem as (Hall & Hpd & Hfr).
  split; [|split].
  - apply Forall_app in Hall as [A1 A2].
    inversion A2 as [|? ? _ A3]; subst. inversion A3 as [|? ? _ A4]; subst.
    apply Forall_app. split; [exact A1|]. constructor; [exact Hoh | exact A4].
  - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *.
    eapply pdr_merge2; [exact Hpd|].
    intros a. rewrite Rng. unfold in_range. cbn [fst snd]. intros Ha.
    destruct (Z_lt_ge_dec a (snd (obj_range rho o1))); [left; lia | right; lia].
  - intros a Ha. apply Hfr.
    assert (LE1 : fst (obj_range rho o1) <= snd (obj_range rho o1)).
    { destruct Ho1 as ((? & ? & ? & ?) & _). unfold obj_range, obj_lo_of, obj_hi_of in *. cbn. lia. }
    assert (LE2 : fst (obj_range rho o2) <= snd (obj_range rho o2)).
    { destruct Ho2 as ((? & ? & ? & ?) & _). unfold obj_range, obj_lo_of, obj_hi_of in *. cbn. lia. }
    pose proof Adj as ADJ.
    assert (COV : forall x, in_range (obj_range rho o) x <->
                   exists o', In o' [o1; o2] /\ in_range (obj_range rho o') x).
    { intros x. rewrite Rng. unfold in_range. cbn [fst snd]. split.
      + intros Hx. destruct (Z_lt_ge_dec x (snd (obj_range rho o1))).
        * exists o1. split; [cbn; auto | lia].
        * exists o2. split; [cbn; auto | lia].
      + intros (o' & Hin & Hx). cbn in Hin. destruct Hin as [<-|[<-|[]]]; lia. }
    apply (proj1 (outside_all_replace rho (firstn i (ss_objs S)) o
             (skipn (Datatypes.S (Datatypes.S i)) (ss_objs S)) [o1; o2] a COV)). exact Ha.
Qed.

End WithSegs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymEntail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Rebase.
Variable segs : list Segment.

Definition shift_ok (facts : list sprop) (x : sv) (c : Z) : bool := ltac2:(tb__ "0|2|
S3eS3fS0S0A2M0A1S3dLx;S5dVfacts;Vx;A2G0G0S3dLp;R1S0S0S46S52S56S50Z2Z3fA2M1A1S4fR2Vc;A2A2S55S4fR1Vc;A2G1A2A2Lh;Ll;X3fx1Lp;S45X3ex2").

Definition shift_off (x : sv) (c : Z) : sv := ltac2:(tb__ "0|0|
S4S4Lx;S5cVx;Vc;A2S0S1fS58R1A1A1Lz;S1S33R1A1Li;S68S4S4S1eR3R2R1A3Lb;La;Lop;S68S4S4S2eR3R2R1A3Lb;La;Lop;S69S4S4S31R3R2R1A3Lb;La;Lop;S69S4S4S32R3R2R1A3Lb;La;Lop;S3dS2S4S2fR3R2R1A3La;Lw;Lsgn;S1S4S0S30R3R2R1A3Lk;Li;Ll;X4x8").

Lemma shift_off_eval : ltac2:(tb__ "0|0|
S8S4S0S37S72Q40A1S12R3S63R2R1A2A2S12R3S5cR2R1A2A2A3Fc;Fx;Frho;").
Proof using .
  intros rho x c. unfold shift_off. destruct (mk_addk x c); try reflexivity.
  cbn. apply Z_to_bv64_snorm.
Qed.

Lemma shift_off_below : ltac2:(tb__ "0|0|
S1S4S0S37S3dS23R3R2A2S43A3S37S3dS23R4S63R3R2A2A2S43A3F_;Fc;Fx;Fn;").
Proof using .
  intros n x c H. unfold shift_off. pose proof (mk_addk_below n x c H) as B.
  destruct (mk_addk x c); first [reflexivity | exact B].
Qed.

Definition shift_cell (c : Z) (cl : cell) : cell := ltac2:(tb__ "0|0|
S35S63S16Vcl;A1Vc;A2S1aVcl;A1S34Vcl;A1A3").

Definition rebase_obj (facts : list sprop) (o : sobj) : option sobj := ltac2:(tb__ "0|d|
S4S3eS3A1M0Lx;S14Vo;A1S0S47S3A1M1Lz;S1G1Li;M2S68S4S4S68G0Lop;R3S4G0Lb;R1S0S58R1A1S0S3fS0S0A2G0Lx;S5bVfacts;R4A2S0S0S3dG0L_;S46S46S46S46S46S46S52R2R1A2S52Z0S4fR2R3A2A2A2S55S4fR1R3A2S50Z2Z40A2A2A2S64Vfacts;SbVo;A1M3R3A3A2S64Vfacts;SaVo;A1M4R3A3A2S61S6S6S64Vfacts;S16R1A1R4A3Lcl;SfVo;A1M5A3A2S4dS13S10Vo;A1M6A1A1A2S40S3SeR6S63G3R3A2S63G4R3A2S76S6S6S66R3A1G5A4G6A5A2G1X3dx2Lh;Ll;X3fx1Tc;Lc0;G2S68S4S4G1Lb0;La0;M7Lop0;M8G8S69G7Lop0;M9G9S3dS2S4G1La0;Lw;Lsgn;S1S4S0G1Lk;Li;Ll;MaX4x8G1G1G1G1G1G1G1G1G1X68xaLb;La;Lop;S68S4S4G1Lb;La;MbLop;S69GbLop;McGcS3dS2S4G1La;Lw;Lsgn;GaX4x8").

Definition rebase_obj_at (S : sstate) (i : nat) : option sstate := ltac2:(tb__ "0|3|
S3eS3A1S3eS7A1Lx;M0S60S3S1bVS;A1M1Vi;A3S3G0S65S22VS;A1R1A2S3S40S7S5aVS;S41S3S75S3Vi;G1A3S44S3R1S77S3S4bVi;A1G1A3A3A3A2A2Lo';S47S7A1M2X3ex2Lo;G2X3ex2").

Lemma snorm_congr : ltac2:(tb__ "0|1|
S0S0S37S0S53R2S50Z2Z40A2M0A2S53R1G0A2A3S37S0S58R3A1S58R2A1A3F_;Fb;Fa;").
Proof using . intros a b H. unfold snorm. rewrite H. reflexivity. Qed.

Lemma soff_mk_addk : ltac2:(tb__ "0|2|
S8S4S0S38S4eS56S50Z2Z3fA2M0A1S4fS9R3R2A2R1A2M1A2S51G1G0A2A2S37S0S9R4S5cR3R2A2A2S4fS9R4R3A2R2A2A3F_;Fc;Fx;Frho;").
Proof using .
  intros rho x c Hr. rewrite !soff_snorm in *. unfold U in *.
  rewrite mk_addk_sound, bv_add_unsigned, lit_unsigned. unfold bv_wrap. rewrite two64.
  rewrite <- (snorm_small (snorm (bv_unsigned (eval rho x)) + c)) by exact Hr.
  apply snorm_congr. rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
  rewrite <- (Zplus_mod_idemp_l (snorm (bv_unsigned (eval rho x)))), snorm_mod, Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma shift_ok_sound : ltac2:(tb__ "0|0|
S8S42S18A1S4S0S74S18S27R4A1R3A3S37S3dS64R4R3R2A3S43A3S37S0S9R6S63R4R3A2A2S4fS9R6R4A2R3A2A3F_;F_;Fc;Fx;Ffacts;Frho;").
Proof using .
  intros rho facts x c Hf H. unfold shift_ok in H.
  destruct (sitv facts x) as [[l h]|] eqn:Hs; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof (sitv_sound rho facts x l h Hf Hs) as (A & _ & _).
  unfold soff at 1. rewrite shift_off_eval. fold (soff rho (mk_addk x c)).
  apply soff_mk_addk. lia.
Qed.

Lemma rebase_obj_shape : ltac2:(tb__ "0|4|
S42S18A1S3S3S37S3eS3A1S65R3R2A2S40S3R1A2A3S3aS4S4S3aS0S0S38S37S4S14R5A1S1eS6aR2S1fR1A1A3A3S58R1A1S0S3fS0S0A2OLx;S5bR7R3A2S0S0S38S4eR2R1A2S38S4eZ0S4fR2R3A2A2S38S51S4fR1R3A2S50Z2Z40A2A2S38S37S3dS64R9SbR8A1M0R3A3S43A3S38S37S3dS64R9SaR8A1M1R3A3S43A3S38S37S3dS61S6S6S64RaS16R1A1R4A3Lcl;SfR8A1M2A3S43A3S38S37S3dS13S10R8A1M3A1S45A3S37S3R7SeR5S63G0R3A2S63G1R3A2S76S6S6S66R3A1G2A4G3A5A3A2A2A2A2A2A2A2Lh;Ll;X3fx1Tc;A2Lc0;A2La;A2F_;Fo';Fo;Ffacts;").
Proof using .
  intros facts o o' H. unfold rebase_obj in H.
  destruct (ob_base o) as [| |op a b| | | | |] eqn:Hb; try discriminate.
  destruct op; try discriminate. destruct b as [c0| | | | | | |]; try discriminate.
  exists a, c0. split; [reflexivity|]. cbn zeta.
  destruct (itv facts a) as [l h].
  destruct (Z.leb_spec l h); [|discriminate].
  destruct (Z.leb_spec 0 (l + snorm c0)); [|discriminate].
  destruct (Z.ltb_spec (h + snorm c0) (2 ^ 64)); [|discriminate]. cbn [andb] in H.
  destruct (shift_ok facts (ob_lo o) (snorm c0)); [|discriminate].
  destruct (shift_ok facts (ob_hi o) (snorm c0)); [|discriminate].
  destruct (forallb (fun cl => shift_ok facts (c_off cl) (snorm c0)) (ob_cells o)); [|discriminate].
  destruct (is_arr (ob_dflt o)); [discriminate|].
  cbn [andb negb] in H. injection H as <-. repeat split; auto.
Qed.

Lemma rebase_base_val : ltac2:(tb__ "0|2|
S8S42S18A1S4S0S74S18S27R4A1R3A3S3fS0S0A2OLx;S5bR4R3A2S0S0S38S4eR2R1A2S38S4eZ0S4fR2S58R4A1M0A2A2S51S4fR1G0A2S50Z2Z40A2A2A2A2Lh;Ll;X3fx1S37S0S73Q40M1S12R6S1eS6aR4S1fR3A1A3A2A2S4fS73G1S12R6R4A2A2S58R3A1A2A3F_;F_;Fc0;Fa;Ffacts;Frho;").
Proof using .
  intros rho facts a c0 Hf H.
  pose proof (itv_sound rho facts a Hf) as I. destruct (itv facts a) as [l h]. unfold in_itv in I. cbn in I.
  destruct H as (H1 & H2 & H3).
  cbn [eval]. rewrite add_lit_val. apply Z.mod_small. lia.
Qed.

Theorem smatch_rebase : ltac2:(tb__ "0|0|
S8S7S4cS7S3fS42S79A1S78A2S37S3eS7A1S67R4R3A2S40S7R2A2A3S15Vsegs;R6R5R2A4S15Vsegs;R7R4R3A4F_;F_;Fw;FS';Fi;FS;Frho;").
Proof using .
  intros rho S i S' [tr [ms md]] Hrb Hsm.
  unfold rebase_obj_at in Hrb.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hn; [|discriminate].
  destruct (rebase_obj (ss_facts S) o) as [o'|] eqn:Ho; [|discriminate]. injection Hrb as <-.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 _ _ _ Hn) as EQ.
  assert (Hwfo : obj_wf (ss_next S) o = true).
  { pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [_ W]. apply andb_prop in W as [W _]. exact W. }
  assert (Hoh : obj_holds segs rho ms o).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall]. inversion Hall; auto. }
  destruct (rebase_obj_shape _ _ _ Ho) as (a & c0 & Hbase & Hsh).
  cbn zeta in Hsh. destruct (itv (ss_facts S) a) as [l h] eqn:Hitv.
  destruct Hsh as (Hlh & Hl & Hh & Slo & Shi & Scells & NA & Eo').
  set (c := snorm c0) in *.
  assert (Hb : bv_unsigned (eval rho (ob_base o)) = bv_unsigned (eval rho a) + c).
  { rewrite Hbase. apply (rebase_base_val rho (ss_facts S) a c0 Hfacts). rewrite Hitv. repeat split; assumption. }
  pose proof (shift_ok_sound rho _ _ _ Hfacts Slo) as Elo.
  pose proof (shift_ok_sound rho _ _ _ Hfacts Shi) as Ehi.
  assert (Ecells : forall cl, In cl (ob_cells o) -> soff rho (shift_off (c_off cl) c) = soff rho (c_off cl) + c).
  { intros cl Hcl. apply (shift_ok_sound rho (ss_facts S)); [exact Hfacts|].
    exact (proj1 (forallb_forall _ _) Scells cl Hcl). }
  assert (Hrange : obj_range rho o' = obj_range rho o).
  { rewrite Eo'. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite Elo, Ehi, Hb. f_equal; lia. }
  assert (Hwfo' : obj_wf (ss_next S) o' = true).
  { rewrite Eo'. unfold obj_wf in Hwfo |- *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
    repeat (apply andb_prop in Hwfo; destruct Hwfo as [Hwfo ?]).
    rewrite Hbase in Hwfo. cbn in Hwfo. apply andb_prop in Hwfo as [Ha _].
    rewrite Ha, (shift_off_below _ _ _ H2), (shift_off_below _ _ _ H1), H, Bool.andb_true_r. cbn [andb].
    apply forallb_forall. intros cl' Hin'. apply in_map_iff in Hin' as (cl & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) H0 cl Hin) as W. unfold cell_wf in W |- *. cbn [c_off c_width c_val shift_cell].
    repeat (apply andb_prop in W; destruct W as [W ?]).
    match goal with
    | Hw : (0 <? _) = true, Hw8 : (_ <=? 8) = true, Ho : sv_below _ (c_off cl) = true, Hv : sv_below _ (c_val cl) = true |- _ =>
        rewrite Hw, Hw8, Hv, (shift_off_below _ _ _ Ho); reflexivity
    end. }
  assert (Hoh' : obj_holds segs rho ms o').
  { apply (obj_holds_transfer segs rho rho ms o o' (ss_next S) Hrom Hwfo).
    - rewrite Eo'. unfold obj_lo_of. cbn [ob_base ob_lo]. rewrite Elo, Hb. lia.
    - rewrite Eo'. unfold obj_hi_of. cbn [ob_base ob_hi]. rewrite Ehi, Hb. lia.
    - reflexivity.
    - intros c2 Hin2. rewrite Eo' in Hin2. cbn [ob_cells] in Hin2. apply in_map_iff in Hin2 as (c1 & <- & Hin1).
      exists c1. split; [exact Hin1|]. rewrite Eo'. cbn [ob_base]. unfold cell_abs, shift_cell. cbn [c_off c_width c_val].
      rewrite (Ecells c1 Hin1), Hb. f_equal. f_equal. lia.
    - right. left. split; [rewrite Eo'; reflexivity|]. split; [exact NA|]. intros c1 Hin1. exists (shift_cell c c1).
      split; [rewrite Eo'; cbn [ob_cells]; apply in_map; exact Hin1|].
      rewrite Eo'. cbn [ob_base]. unfold cell_abs, shift_cell. cbn [c_off c_width c_val].
      rewrite (Ecells c1 Hin1), Hb. f_equal. f_equal. lia.
    - exact Hoh. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
    eapply swf_objs_replace; [exact Hwf | exact EQ |]. cbn. rewrite Hwfo'. reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
  apply mem_match_replace with (o := o).
  - exact Hmem.
  - constructor; [exact Hoh'|]. constructor.
  - destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite Hrange. exact Hpd.
  - intros x. split.
    + intros Hx. exists o'. split; [cbn; auto|]. rewrite Hrange. exact Hx.
    + intros (o'' & Hin'' & Hx). destruct Hin'' as [<-|[]]. rewrite Hrange in Hx. exact Hx.
Qed.

End Rebase.
