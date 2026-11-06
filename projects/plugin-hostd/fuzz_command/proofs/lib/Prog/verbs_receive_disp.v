From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import VerbsMem VerbsFacts verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strcmp_c strcspn_c strncmp_c verb_is_c is_instance_verb_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require VerbsB.
Import ListNotations.
Open Scope Z_scope.

Definition DISPATCH : Z := 0x17514.
Definition VR_DK : Z := 160.
Definition IMG_TOP : Z := 0x54cb8.

Definition ntokw (tk : list (list byte)) : word := Z_to_bv 64 (Z.of_nat (length tk)).

Definition vr_disp (m : word -> option byte) (lo : Z) (sp msg : word) (D : list byte) (fdw : word) (ps : list word)
    (can : word) : Prop :=
  toks D <> [] /\ Z.of_nat (length D) <= 8192 /\
  bytes_at rsegs m (bv_unsigned msg) (le4 fdw) /\
  bytes_at rsegs m (bv_unsigned sp + 8) (concat (map le8 ps)) /\
  Forall2 (fun p w => cstr0_at m (bv_unsigned p) w /\ off_lo lo sp (bv_unsigned p) (Z.of_nat (length w + 1))) ps (toks D) /\
  bytes_at rsegs m IV_TABLE (concat (map (fun p => le8 (Z_to_bv 64 p)) iv_ptrs)) /\
  bytes_at rsegs m VerbsB.INFO_TABLE VerbsB.info_bytes /\
  ssp_at m can /\
  mem_inv rsegs m /\ stk rsegs m lo (bv_unsigned sp) /\ lo + VR_DK <= bv_unsigned sp /\ IMG_TOP <= lo.

Definition route_regs (r : vroute) (n : nat) (s0 a0 a1 s6 : word) : Prop :=
  match r with
  | RLedger led => a0 = s0 /\ a1 = Z_to_bv 64 led
  | RInst | RConn | RBroad => True
  | _ => s6 = Z_to_bv 64 (Z.of_nat n - 1)
  end.

Definition vr_routed (sp gp tp s0 s1 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z)
    (m : word -> option byte) (fdw p0 : word) (tk : list (list byte)) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' s8' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  (sx32 fdw) (ntokw tk) p0 (ntokw tk) s6' s7' s8' s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 (route_pc (route tk))) fc None m' (seg_rom rsegs) /\
    route_regs (route tk) (length tk) s0 a0' a1' s6' /\
    munch [(bv_unsigned sp - VR_DK, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

Lemma bwin : forall m m' lo (sp : word) a bs,
  bytes_at rsegs m a bs -> off_lo lo sp a (Z.of_nat (length bs)) -> lo + VR_DK <= bv_unsigned sp ->
  munch [(bv_unsigned sp - VR_DK, bv_unsigned sp)] m m' -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo sp a bs H O L M. eapply bytes_at_transport; [exact H | exact M |].
  unfold off_lo, VR_DK in *. cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma read_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  cbn [skipn Z.of_nat] in R. rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

Lemma img_str : forall m p f, mem_inv rsegs m ->
  ((0 <=? p) && (p + Z.of_nat (length f) + 1 <=? 2^64) && ro_bytes_b rsegs p (f ++ [Z_to_bv 8 0]) &&
   forallb (fun b => negb (bv_unsigned b =? 0)) f)%bool = true ->
  bytes_at rsegs m p (f ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) f.
Proof.
  intros m p f HM H. apply andb_true_iff in H. destruct H as [H H4]. apply andb_true_iff in H. destruct H as [H H3].
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. split.
  - apply ro_bytes_at; [exact HM | lia | rewrite length_app; cbn [length]; lia | apply ro_bytes_b_sound; exact H3].
  - intros Hin. rewrite forallb_forall in H4. specialize (H4 _ Hin). vm_compute in H4. discriminate.
Qed.

Definition slack_of (p : Z) (f : list byte) : nat := Z.to_nat ((- (p + Z.of_nat (length f) + 1)) mod 8).

Definition img_cstr_b (p : Z) (f : list byte) : bool :=
  match image_bytes rsegs (p + Z.of_nat (length f) + 1) (slack_of p f) with
  | Some fs => (0 <=? p) && (p + Z.of_nat (length f) + 9 <=? IMG_TOP) &&
               ro_bytes_b rsegs p (f ++ Z_to_bv 8 0 :: fs) && forallb (fun b => negb (bv_unsigned b =? 0)) f
  | None => false
  end.

Lemma img_cstr : forall m lo (sp : word) p f, mem_inv rsegs m -> IMG_TOP <= lo -> img_cstr_b p f = true ->
  exists fs, cstr_at m p f fs /\ off_lo lo sp p (Z.of_nat (length f + 1 + length fs)).
Proof.
  intros m lo sp p f HM HL H. unfold img_cstr_b in H.
  destruct (image_bytes rsegs (p + Z.of_nat (length f) + 1) (slack_of p f)) as [fs|] eqn:E; [|discriminate].
  pose proof (image_bytes_length rsegs _ _ _ E) as LF.
  apply andb_true_iff in H. destruct H as [H H4]. apply andb_true_iff in H. destruct H as [H H3].
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  unfold IMG_TOP in *.
  assert (LS : (slack_of p f < 8)%nat).
  { unfold slack_of. pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length f) + 1)) 8 ltac:(lia)). lia. }
  exists fs. split; [unfold cstr_at; split; [|split]|].
  - apply ro_bytes_at; [exact HM | lia | | apply ro_bytes_b_sound; exact H3].
    rewrite length_app. cbn [length]. unfold IMG_TOP in H2. lia.
  - rewrite Forall_forall. intros b Hb. rewrite forallb_forall in H4. specialize (H4 _ Hb).
    apply negb_true_iff, Z.eqb_neq in H4. exact H4.
  - rewrite LF. unfold slack_of. pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length f) + 1)) 8 ltac:(lia)). lia.
  - unfold off_lo. left. lia.
Qed.

Lemma cstr_cstr0 : forall m p f fs, cstr_at m p f fs -> bytes_at rsegs m p (f ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) f.
Proof.
  intros m p f fs H. unfold cstr_at in H. destruct H as (H1 & H2 & _). split.
  - replace (f ++ Z_to_bv 8 0 :: fs) with ((f ++ [Z_to_bv 8 0]) ++ fs) in H1 by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in H1. exact (proj1 H1).
  - intros Hin. rewrite Forall_forall in H2. apply (H2 _ Hin). reflexivity.
Qed.

Lemma nz_notin : forall l, Forall (fun b : byte => bv_unsigned b <> 0) l -> ~ In (Z_to_bv 8 0) l.
Proof. intros l H Hin. rewrite Forall_forall in H. apply (H _ Hin). reflexivity. Qed.

Ltac fix_ret :=
  lazymatch goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (apply bv_eq; vm_compute; reflexivity)
  end.

Lemma nz_lit : forall f, forallb (fun b => negb (bv_unsigned b =? 0)) f = true -> ~ In (Z_to_bv 8 0) f.
Proof. intros f H Hin. rewrite forallb_forall in H. specialize (H _ Hin). vm_compute in H. discriminate. Qed.

Lemma img_bytes : forall m p bs, mem_inv rsegs m ->
  ((0 <=? p) && (p + Z.of_nat (length bs) <=? 2^64) && ro_bytes_b rsegs p bs)%bool = true -> bytes_at rsegs m p bs.
Proof.
  intros m p bs HM H. apply andb_true_iff in H. destruct H as [H H3]. apply andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply ro_bytes_at; [exact HM | lia | lia | apply ro_bytes_b_sound; exact H3].
Qed.

Lemma bv_eqb_true : forall x y : word, bv_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold bv_eqb. rewrite Z.eqb_eq. split; [apply bv_eq | intros ->; reflexivity].
Qed.

Lemma scmp_eqb : forall (r : word) v L, (r = Z_to_bv 64 0 <-> v = L) -> bv_eqb r (Z_to_bv 64 0) = list_eqb v L.
Proof.
  intros r v L H. apply eq_true_iff_eq. rewrite bv_eqb_true, list_eqb_eq. exact H.
Qed.

Lemma eqb_lit : forall (x : nat) c, Z.of_nat x < 2^64 -> 0 <= c < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.of_nat x)) (Z_to_bv 64 c) = (Z.of_nat x =? c).
Proof. intros x c Hx Hc. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma eqb_small : forall w, -256 < w < 256 -> bv_eqb (Z_to_bv 64 w) (Z_to_bv 64 0) = (w =? 0).
Proof.
  intros w Hw. unfold bv_eqb. rewrite (unsigned_lit 0) by lia. rewrite unsigned_lit_wrap.
  destruct (Z.eqb_spec w 0) as [->|E]; [reflexivity|]. apply Z.eqb_neq. intros C. apply E.
  Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_ite : forall b : bool, bv_eqb (Z_to_bv 64 (if b then 1 else 0)) (Z_to_bv 64 0) = negb b.
Proof. intros []; reflexivity. Qed.

Lemma munch_nil : forall W (m m' : word -> option byte), munch [] m m' -> munch W m m'.
Proof. intros W m m' H. eapply munch_weaken; [|exact H]. intros x _. exact I. Qed.

Lemma munch_sub : forall (m m' : word -> option byte) lo hi lo' hi',
  lo' <= lo -> hi <= hi' -> munch [(lo, hi)] m m' -> munch [(lo', hi')] m m'.
Proof.
  intros m m' lo hi lo' hi' L H M. eapply munch_weaken; [|exact M].
  intros x [Hx _]. split; [lia | exact I].
Qed.

Lemma info_chunks : forall i, (i < 10)%nat ->
  firstn 8 (skipn (16 * i) VerbsB.info_bytes) = le8 (Z_to_bv 64 (fst (nth i VerbsB.info_rows (0, 0)))) /\
  firstn 4 (skipn (16 * i + 8) VerbsB.info_bytes) = le4 (Z_to_bv 64 (snd (nth i VerbsB.info_rows (0, 0)))).
Proof. intros i Hi. do 10 (destruct i as [|i]; [split; vm_compute; reflexivity|]). lia. Qed.

Lemma info_rd : forall mk i, bytes_at rsegs mk VerbsB.INFO_TABLE VerbsB.info_bytes -> (i < 10)%nat ->
  ov_read_bytes rsegs mk (wa (VerbsB.INFO_TABLE + Z.of_nat (16 * i))) 8 =
    Some (le8 (Z_to_bv 64 (fst (nth i VerbsB.info_rows (0, 0))))) /\
  ov_read_bytes rsegs mk (wa (VerbsB.INFO_TABLE + Z.of_nat (16 * i + 8))) 4 =
    Some (le4 (Z_to_bv 64 (snd (nth i VerbsB.info_rows (0, 0))))).
Proof.
  intros mk i H Hi. destruct (info_chunks i Hi) as [C1 C2].
  assert (LB : length VerbsB.info_bytes = 160%nat) by (vm_compute; reflexivity).
  split; [rewrite <- C1 | rewrite <- C2]; apply bytes_at_ov_read; (exact H || lia).
Qed.

Lemma len3 : forall (v : list byte) args, Z.of_nat (length (v :: args)) = 3 -> exists a b, args = [a; b].
Proof. intros v [|a [|b [|c r]]] H; cbn [length] in H; try lia. exists a, b. reflexivity. Qed.

Lemma route_cd_other : forall v args, Z.of_nat (length (v :: args)) <> 3 -> route_cd v args = RBroad.
Proof. intros v [|a [|b [|c r]]] H; cbn [length] in H; try reflexivity. lia. Qed.


Lemma eqb_ntokw : forall tk c, (length tk <= 64)%nat -> 0 <= c < 2^64 ->
  bv_eqb (ntokw tk) (Z_to_bv 64 c) = (Z.of_nat (length tk) =? c).
Proof. intros tk c Ht Hc. unfold ntokw. apply eqb_lit; lia. Qed.

Lemma route_conn_cons : forall v args, args <> [] -> route_conn v args = if is_instance_verb v then RInst else route_cd v args.
Proof. intros v [|a r] H; [congruence|]. reflexivity. Qed.

Lemma len1 : forall (v : list byte) args, Z.of_nat (length (v :: args)) = 1 -> args = [].
Proof. intros v [|a r] H; cbn [length] in H; [reflexivity | lia]. Qed.

Lemma len_not1 : forall (v : list byte) args, Z.of_nat (length (v :: args)) <> 1 -> args <> [].
Proof. intros v [|a r] H; cbn [length] in H; [lia | discriminate]. Qed.

Lemma route_tail_none : forall v args, ledger_of v instance_info_verbs = None -> route_tail v args = route_conn v args.
Proof. intros v args H. unfold route_tail. rewrite H. reflexivity. Qed.

Ltac ledger_none_tac :=
  cbv beta iota delta [ledger_of instance_info_verbs];
  repeat match goal with H : ?b = false |- context [?b] => rewrite H end; reflexivity.

Ltac info_name i := eval cbv beta iota delta [nth map fst instance_info_verbs] in (nth i (map fst instance_info_verbs) []).
Ltac info_led i := eval cbv beta iota delta [nth map snd instance_info_verbs] in (nth i (map snd instance_info_verbs) 0).

Section Disp.
Hypothesis SCMP : strcmp_contract.
Hypothesis CSPN : strcspn_contract.
Hypothesis NCMP : strncmp_contract.
Hypothesis VIS : verb_is_contract.
Hypothesis IIV : is_instance_verb_contract.
Variables (sp gp tp s0 s1 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
  (fdw p0 : word) (v : list byte) (args : list (list byte)) (can : word).
Hypothesis HV : cstr0_at m (bv_unsigned p0) v.
Hypothesis OV : off_lo lo sp (bv_unsigned p0) (Z.of_nat (length v + 1)).
Hypothesis VL : Z.of_nat (length v) + 1 < 2^62.
Hypothesis HIV : bytes_at rsegs m IV_TABLE (concat (map (fun p => le8 (Z_to_bv 64 p)) iv_ptrs)).
Hypothesis HINFO : bytes_at rsegs m VerbsB.INFO_TABLE VerbsB.info_bytes.
Hypothesis HSSP : ssp_at m can.
Hypothesis LO : lo + VR_DK <= bv_unsigned sp.
Hypothesis HIT : IMG_TOP <= lo.
Hypothesis NL : (length (v :: args) <= 64)%nat.

Definition minv (mk : word -> option byte) : Prop :=
  munch [(bv_unsigned sp - VR_DK, bv_unsigned sp)] m mk /\ wmono rsegs m mk /\ mem_inv rsegs mk /\
  stk rsegs mk lo (bv_unsigned sp).

Lemma minv_call : forall mk mk' K, minv mk -> K <= VR_DK -> munch [(bv_unsigned sp - K, bv_unsigned sp)] mk mk' ->
  wmono rsegs mk mk' -> mem_inv rsegs mk' -> stk rsegs mk' lo (bv_unsigned sp) -> minv mk'.
Proof.
  intros mk mk' K (M & W & _ & _) HK M' W' I' S'. split; [|split; [|split]].
  - eapply munch_trans; [exact M|]. eapply munch_sub; [| | exact M']; lia.
  - eapply wmono_trans; eassumption.
  - exact I'.
  - exact S'.
Qed.

Lemma minv_call0 : forall mk mk', minv mk -> munch [] mk mk' -> wmono rsegs mk mk' -> mem_inv rsegs mk' -> minv mk'.
Proof.
  intros mk mk' (M & W & HI & S) M' W' I'. split; [|split; [|split]].
  - eapply munch_trans; [exact M|]. apply munch_nil. exact M'.
  - eapply wmono_trans; eassumption.
  - exact I'.
  - eapply stk_transport_disjoint; [exact S | exact M' | exact W' | exact I].
Qed.

Lemma win : forall mk a bs, minv mk -> bytes_at rsegs m a bs -> off_lo lo sp a (Z.of_nat (length bs)) ->
  bytes_at rsegs mk a bs.
Proof. intros mk a bs (M & _) H O. eapply bwin; [exact H | exact O | exact LO | exact M]. Qed.

Lemma win_v : forall mk, minv mk -> cstr0_at mk (bv_unsigned p0) v.
Proof.
  intros mk H. destruct HV as [H1 H2]. split; [|exact H2]. apply (win mk _ _ H H1).
  rewrite length_app. cbn [length]. exact OV.
Qed.

Lemma win_ssp : forall mk, minv mk -> ssp_at mk can.
Proof.
  intros mk H. destruct HSSP as [H1 H2]. unfold IMG_TOP in HIT. split; apply (win mk _ _ H);
    (assumption || (rewrite length_le8; unfold off_lo, SSP_GOT, SSP_GUARD; lia)).
Qed.

Lemma win_info : forall mk, minv mk -> bytes_at rsegs mk VerbsB.INFO_TABLE VerbsB.info_bytes.
Proof.
  intros mk H. apply (win mk _ _ H HINFO). unfold IMG_TOP in HIT.
  assert (LB : length VerbsB.info_bytes = 160%nat) by (vm_compute; reflexivity).
  rewrite LB. unfold off_lo, VerbsB.INFO_TABLE. lia.
Qed.

Lemma win_iv : forall mk, minv mk -> bytes_at rsegs mk IV_TABLE (concat (map (fun p => le8 (Z_to_bv 64 p)) iv_ptrs)).
Proof.
  intros mk H. apply (win mk _ _ H HIV). unfold IMG_TOP in HIT.
  assert (LB : length (concat (map (fun p => le8 (Z_to_bv 64 p)) iv_ptrs)) = 144%nat) by (vm_compute; reflexivity).
  rewrite LB. unfold off_lo, IV_TABLE. lia.
Qed.

Lemma iv_fmts : forall mk, mem_inv rsegs mk ->
  Forall2 (fun p f => exists fs, cstr_at mk p f fs /\ off_lo lo sp p (Z.of_nat (length f + 1 + length fs)))
          iv_ptrs instance_verb_formats.
Proof.
  intros mk HM. unfold iv_ptrs, instance_verb_formats. cbn [map].
  repeat (apply Forall2_cons; [apply img_cstr; [exact HM | exact HIT | vm_compute; reflexivity] |]).
  apply Forall2_nil.
Qed.

Let Q := vr_routed sp gp tp s0 s1 s9 s10 s11 F fc lo m fdw p0 (v :: args).

Ltac cur_v :=
  lazymatch goal with
  | |- bytes_at _ ?mk _ _ => lazymatch goal with H : cstr0_at mk _ v |- _ => exact (proj1 H) end
  end.

Ltac lit_at :=
  rewrite ?unsigned_lit by lia; refine (proj1 (img_str _ _ _ _ _)); [eassumption | vm_compute; reflexivity].

Ltac scmp_call L :=
  eapply evt_cut;
  [ eapply SCMP with (sx := v) (sy := L);
    [ cur_v | apply nz_notin; exact (proj2 HV) | lit_at | apply nz_lit; vm_compute; reflexivity ]
  | intros ms' (?r & ?x11 & ?x12 & ?x13 & ?E & HRc); subst ms'; fix_ret ].

Ltac route_eq :=
  first [ match goal with RT : route _ = _ |- _ => rewrite RT end | unfold route ];
  unfold route_mid, route_tail, route_conn, route_cd;
  cbv beta iota delta [ledger_of instance_info_verbs];
  repeat match goal with
  | H : ?b = false |- context [?b] => rewrite H
  | H : ?b = true |- context [?b] => rewrite H
  end; reflexivity.

Ltac fin R :=
  apply evt_done; unfold Q, vr_routed;
  replace (route (v :: args)) with R by route_eq;
  cbn [route_pc route_regs];
  do 20 eexists; split; [reflexivity|];
  split; [ first [ exact I | reflexivity | eassumption | split; reflexivity ] | ];
  split; [eassumption|]; split; [eassumption|]; split; eassumption.

Ltac chk_tail L R :=
  zstep;
  match goal with H : (_ = Z_to_bv 64 0 <-> _) |- _ => rewrite (scmp_eqb _ _ _ H); clear H end;
  let EQ := fresh "EQ" in destruct (list_eqb v L) eqn:EQ; cbv iota; [fin R |].

Ltac chk L R := do 4 zstep; scmp_call L; chk_tail L R.

Ltac offs := unfold off_lo, IMG_TOP, VR_DK, VERB_IS_K, IS_INSTANCE_VERB_K, SSP_GOT, SSP_GUARD, IV_TABLE,
  CSPN_SSP_GOT, CSPN_SSP_GUARD,
  verb_is_c.DS_STR, verb_is_c.DT_STR, is_instance_verb_c.DS_STR, is_instance_verb_c.DT_STR in *; lia.

Ltac newmem HMk K mv MUv WMv MIv STv :=
  let HMn := fresh "HM" in
  assert (HMn : minv mv) by (refine (minv_call _ mv K HMk _ MUv WMv MIv STv); offs);
  clear MUv WMv;
  let a := fresh "MU" in let b := fresh "WM" in
  pose proof HMn as (a & b & _ & _);
  let c := fresh "HVc" in pose proof (win_v mv HMn) as c;
  let d := fresh "HSc" in pose proof (win_ssp mv HMn) as d.

Ltac vis_call A f :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mk _) =>
  lazymatch goal with HMk : minv mk |- _ =>
  let fsl := fresh "fs" in let HF := fresh "HF" in let OF := fresh "OF" in
  destruct (img_cstr mk lo sp A f ltac:(eassumption) HIT ltac:(vm_compute; reflexivity)) as (fsl & HF & OF);
  eapply evt_cut;
  [ eapply VIS with (tb := v) (fb := f) (fs := fsl) (lo := lo) (can := can);
    [ eassumption
    | rewrite unsigned_lit by lia; exact HF
    | exact VL
    | apply Z.ltb_lt; vm_compute; reflexivity
    | apply img_bytes; [eassumption | vm_compute; reflexivity]
    | apply img_bytes; [eassumption | vm_compute; reflexivity]
    | eassumption
    | offs
    | offs
    | eassumption
    | eassumption
    | offs
    | exact OV
    | rewrite unsigned_lit by lia; exact OF
    | offs
    | offs ]
  | let ms' := fresh "ms'" in let PO := fresh "PO" in
    let mv := fresh "mv" in let MUv := fresh "MUv" in let WMv := fresh "WMv" in
    let MIv := fresh "MIv" in let STv := fresh "STv" in let E := fresh "E" in
    intros ms' PO; unfold kret in PO;
    destruct PO as (?t0' & ?t1' & ?t2' & ?a0' & ?a1' & ?a2' & ?a3' & ?a4' & ?a5' & ?a6' & ?a7' & ?t3' & ?t4' & ?t5' &
                    ?t6' & mv & E & MUv & WMv & MIv & STv & ->);
    subst ms'; fix_ret; clear HF OF;
    newmem HMk VERB_IS_K mv MUv WMv MIv STv ]
  end end.

Ltac fin_by R TAC :=
  apply evt_done; unfold Q, vr_routed;
  replace (route (v :: args)) with R by TAC;
  cbn [route_pc route_regs];
  do 20 eexists; split; [reflexivity|];
  split; [ first [ exact I | reflexivity | eassumption | split; reflexivity ] | ];
  split; [eassumption|]; split; [eassumption|]; split; eassumption.

Lemma part_c : forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word),
  minv mk -> route (v :: args) = route_cd v args ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (sx32 fdw) (ntokw (v :: args)) p0 (ntokw (v :: args))
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17a84) fc None mk (seg_rom rsegs)).
Proof.
  intros mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 HM RT.
  pose proof HM as (MUk & WMk & MIk & STk).
  pose proof (win_v mk HM) as HVc. pose proof (win_ssp mk HM) as HSc.
  assert (NLZ : Z.of_nat (length (v :: args)) < 2^64) by lia.
  do 4 zstep.
  vis_call 0x105fd fmt_connect.
  zstep. rewrite eqb_ite.
  destruct (verb_is_m v fmt_connect) eqn:EC; cbv beta iota delta [negb].
  - do 2 zstep. rewrite eqb_ntokw by lia.
    destruct (Z.of_nat (length (v :: args)) =? 3) eqn:L3; cbv iota.
    + apply Z.eqb_eq in L3. destruct (len3 v args L3) as (a & b & Hargs).
      fin_by RConn ltac:(rewrite RT, Hargs; cbn [route_cd]; rewrite EC; reflexivity).
    + apply Z.eqb_neq in L3. zstep.
      fin_by RBroad ltac:(rewrite RT; symmetry; apply route_cd_other; exact L3).
  - do 4 zstep.
    vis_call 0x10589 fmt_disconnect.
    do 2 zstep. rewrite eqb_ntokw by lia.
    destruct (Z.of_nat (length (v :: args)) =? 3) eqn:L3; cbv beta iota delta [negb].
    + apply Z.eqb_eq in L3. destruct (len3 v args L3) as (a & b & Hargs).
      zstep. rewrite eqb_ite.
      destruct (verb_is_m v fmt_disconnect) eqn:ED; cbv beta iota delta [negb].
      * fin_by RConn ltac:(rewrite RT, Hargs; cbn [route_cd]; rewrite EC, ED; reflexivity).
      * fin_by RBroad ltac:(rewrite RT, Hargs; cbn [route_cd]; rewrite EC, ED; reflexivity).
    + apply Z.eqb_neq in L3.
      fin_by RBroad ltac:(rewrite RT; symmetry; apply route_cd_other; exact L3).
Qed.

Ltac iiv_call :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mk _) =>
  lazymatch goal with HMk : minv mk |- _ =>
  eapply evt_cut;
  [ eapply IIV with (lo := lo) (can := can) (tb := v);
    [ eassumption | exact VL | apply win_iv; exact HMk | apply iv_fmts; eassumption
    | apply img_bytes; [eassumption | vm_compute; reflexivity]
    | apply img_bytes; [eassumption | vm_compute; reflexivity]
    | eassumption | offs | offs | eassumption | eassumption | offs | exact OV | offs | offs | offs ]
  | let ms' := fresh "ms'" in let PO := fresh "PO" in
    let mv := fresh "mi" in let MUv := fresh "MUv" in let WMv := fresh "WMv" in
    let MIv := fresh "MIv" in let STv := fresh "STv" in let E := fresh "E" in
    intros ms' PO; unfold kret in PO;
    destruct PO as (?t0' & ?t1' & ?t2' & ?a0' & ?a1' & ?a2' & ?a3' & ?a4' & ?a5' & ?a6' & ?a7' & ?t3' & ?t4' & ?t5' &
                    ?t6' & mv & E & MUv & WMv & MIv & STv & ->);
    subst ms'; fix_ret;
    newmem HMk IS_INSTANCE_VERB_K mv MUv WMv MIv STv ]
  end end.

Ltac ledger_iter i :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mk _) =>
  lazymatch goal with HMk : minv mk |- _ =>
  let HIk := fresh "HIk" in pose proof (win_info mk HMk) as HIk;
  let RD := fresh "RD" in let RL := fresh "RL" in
  destruct (info_rd mk i HIk ltac:(lia)) as [RD RL];
  cbv beta iota delta [nth VerbsB.info_rows fst snd] in RD, RL;
  let L := info_name i in
  let led := info_led i in
  do 3 zstep; clear RD;
  scmp_call L;
  zstep;
  match goal with H : (_ = Z_to_bv 64 0 <-> _) |- _ => rewrite (scmp_eqb _ _ _ H); clear H end;
  let EQ := fresh "EQ" in destruct (list_eqb v L) eqn:EQ; cbv iota;
  [ do 2 zstep; fin (RLedger led) | clear RL HIk; do 3 zstep; first [if_true | if_false] ]
  end end.

Lemma part_b2 : forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word),
  minv mk -> route (v :: args) = route_tail v args ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (sx32 fdw) (ntokw (v :: args)) p0 (ntokw (v :: args))
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17a24) fc None mk (seg_rom rsegs)).
Proof.
  intros mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 HM RT.
  pose proof HM as (MUk & WMk & MIk & STk).
  pose proof (win_v mk HM) as HVc. pose proof (win_ssp mk HM) as HSc.
  assert (NLZ : Z.of_nat (length (v :: args)) < 2^64) by lia.
  do 3 zstep.
  ledger_iter 0%nat. ledger_iter 1%nat. ledger_iter 2%nat. ledger_iter 3%nat. ledger_iter 4%nat.
  ledger_iter 5%nat. ledger_iter 6%nat. ledger_iter 7%nat. ledger_iter 8%nat. ledger_iter 9%nat.
  assert (LN : ledger_of v instance_info_verbs = None) by ledger_none_tac.
  rewrite (route_tail_none v args LN) in RT.
  do 2 zstep.
  iiv_call.
  change (existsb (verb_is_m v) instance_verb_formats) with (is_instance_verb v).
  do 2 zstep. rewrite eqb_ntokw by lia.
  destruct (Z.of_nat (length (v :: args)) =? 1) eqn:L1; cbv iota.
  - apply Z.eqb_eq in L1. pose proof (len1 v args L1) as A0.
    eapply part_c; [eassumption |]. rewrite RT, A0. reflexivity.
  - apply Z.eqb_neq in L1. pose proof (len_not1 v args L1) as A1.
    rewrite (route_conn_cons v args A1) in RT.
    zstep. rewrite eqb_ite.
    destruct (is_instance_verb v) eqn:II; cbv beta iota delta [negb].
    + fin_by RInst ltac:(rewrite RT; reflexivity).
    + eapply part_c; [eassumption | exact RT].
Qed.

Lemma part_b : forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word),
  minv mk -> route (v :: args) = route_mid v args -> s6 = Z_to_bv 64 (Z.of_nat (length (v :: args)) - 1) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (sx32 fdw) (ntokw (v :: args)) p0 (ntokw (v :: args))
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1758c) fc None mk (seg_rom rsegs)).
Proof.
  intros mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 HM RT HS6.
  pose proof HM as (MUk & WMk & MIk & STk).
  pose proof (win_v mk HM) as HVc. pose proof (win_ssp mk HM) as HSc.
  chk verb_worker_list RWlist.
  chk verb_instance_info RIinfo.
  chk verb_supervisor_reset RReset.
  chk verb_quarantine_clear RQclear.
  chk verb_policy_set RPolicy.
  chk verb_lv2_worker_set RLv2.
  chk verb_pool_config RPool.
  chk verb_worker_env REnv.
  chk verb_chain RChain.
  chk verb_chain_clear RChclear.
  chk verb_pin_set RPinset.
  chk verb_pin_accept RPinacc.
  chk verb_pin_clear RPinclr.
  do 4 zstep.
  vis_call 0x109ef fmt_quit.
  zstep. rewrite eqb_ite.
  destruct (verb_is_m v fmt_quit) eqn:EQq; cbv beta iota delta [negb].
  - fin RQuit.
  - eapply part_b2; [eassumption |].
    rewrite RT. unfold route_mid.
    repeat match goal with H : ?b = false |- context [?b] => rewrite H end. reflexivity.
Qed.

Lemma part_a : forall (msg : word) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 t3 t4 t5 t6 : word),
  bytes_at rsegs m (bv_unsigned msg) (le4 fdw) -> bytes_at rsegs m (bv_unsigned sp + 8) (le8 p0) ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 msg (ntokw (v :: args)) s4 (ntokw (v :: args))
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DISPATCH) fc None m (seg_rom rsegs)).
Proof.
  intros msg ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 t3 t4 t5 t6 HMSG HT0 HMI ST.
  assert (HM : minv m).
  { split; [apply munch_refl | split; [apply wmono_refl | split; assumption]]. }
  pose proof HM as (MUk & WMk & MIk & STk).
  pose proof (win_v m HM) as HVc. pose proof (win_ssp m HM) as HSc.
  assert (NLZ : Z.of_nat (length (v :: args)) < 2^64) by lia.
  pose proof (read_all _ _ _ HMSG) as RDM. rewrite length_le4 in RDM.
  rewrite (wa_of_var msg (bv_unsigned msg) eq_refl) in RDM.
  pose proof (read_all _ _ _ HT0) as RDP. rewrite length_le8 in RDP.
  unfold DISPATCH.
  do 2 zstep. clear RDM RDP.
  do 4 zstep. scmp_call verb_add. zstep.
  assert (HS6 : Z_to_bv 64 (bv_unsigned (ntokw (v :: args)) + -1) = Z_to_bv 64 (Z.of_nat (length (v :: args)) - 1)).
  { unfold ntokw. rewrite unsigned_lit by lia. f_equal; lia. }
  rewrite HS6.
  chk_tail verb_add RAdd.
  chk verb_descriptor_get RDget.
  chk verb_panel_get RPget.
  do 4 zstep.
  eapply evt_cut.
  { eapply CSPN with (str := v) (slack := []) (set := map (Z_to_bv 8) [32; 9]) (lo := lo) (can := can);
    [ cur_v
    | apply nz_notin; exact (proj2 HV)
    | intros Hs; cbn in Hs; lia
    | rewrite unsigned_lit by lia; apply img_bytes; [eassumption | vm_compute; reflexivity]
    | apply nz_lit; vm_compute; reflexivity
    | exact (proj1 HSc)
    | exact (proj2 HSc)
    | eassumption
    | offs
    | cbn [length]; offs
    | rewrite unsigned_lit by lia; cbn [length map]; offs
    | offs
    | offs
    | eassumption ]. }
  intros ms' PO. unfold strcspn_post in PO.
  destruct PO as (?t0' & ?t1' & ?t2' & ?a1' & ?a2' & ?a3' & ?a4' & ?a5' & ?a6' & ?a7' & ?t3' & ?t4' & ?t5' & ?t6' & m2 &
                  E & MU2 & WM2 & MI2 & ST2).
  subst ms'. fix_ret. rewrite cspn_tfirst.
  newmem HM 96 m2 MU2 WM2 MI2 ST2.
  assert (LT : (length (tfirst v) <= length v)%nat) by apply upto_length.
  do 2 zstep. rewrite eqb_lit by lia.
  destruct (Z.of_nat (length (tfirst v)) =? 6) eqn:L6; cbv beta iota delta [negb].
  - apply Z.eqb_eq in L6.
    do 5 zstep.
    destruct (img_cstr m2 lo sp 0x1066c fmt_remove ltac:(eassumption) HIT ltac:(vm_compute; reflexivity))
      as (fsr & HFr & OFr).
    assert (LR : length (tfirst v) = length (vfirst fmt_remove)) by (vm_compute (length (vfirst fmt_remove)); lia).
    destruct (strncmp_verb v fmt_remove fsr (proj2 HV) (proj1 (proj2 HFr)) LR) as (w & HW & RW & QW).
    replace (Z.of_nat (length (vfirst fmt_remove))) with 6 in HW by (vm_compute; reflexivity).
    eapply evt_cut.
    { eapply NCMP with (ls := v ++ [Z_to_bv 8 0]) (rs := fmt_remove ++ Z_to_bv 8 0 :: fsr) (v := w);
      [ cur_v
      | rewrite unsigned_lit by lia; exact (proj1 HFr)
      | rewrite unsigned_lit by lia; exact HW
      | eassumption ]. }
    intros ms' PO. unfold strncmp_post in PO.
    destruct PO as (?t0' & ?t1' & ?t2' & ?a1' & ?a2' & ?a3' & ?a4' & ?a5' & ?a6' & ?a7' & ?t3' & ?t4' & ?t5' & ?t6' & m3 &
                    E & MU3 & WM3 & MI3 & _ & _).
    subst ms'. fix_ret.
    assert (HM3 : minv m3) by (eapply minv_call0; eassumption).
    pose proof HM3 as (MUm3 & WMm3 & _ & STm3).
    zstep. rewrite eqb_small by exact RW. rewrite QW.
    destruct (verb_is_m v fmt_remove) eqn:ER; cbv iota.
    + fin RRemove.
    + eapply part_b; [exact HM3 | | reflexivity].
      unfold route. repeat match goal with H : ?b = false |- context [?b] => rewrite H end. reflexivity.
  - apply Z.eqb_neq in L6.
    assert (ER : verb_is_m v fmt_remove = false).
    { apply verb_is_m_len_ne. vm_compute (length (vfirst fmt_remove)). lia. }
    eapply part_b; [eassumption | | reflexivity].
    unfold route. repeat match goal with H : ?b = false |- context [?b] => rewrite H end. reflexivity.
Qed.

End Disp.

Theorem vr_dispatch : strcmp_contract -> strcspn_contract -> strncmp_contract -> verb_is_contract ->
  is_instance_verb_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (D : list byte) (fdw : word)
         (ps : list word) (can : word),
    vr_disp m lo sp s2 D fdw ps can ->
    evt rsegs (vr_routed sp gp tp s0 s1 s9 s10 s11 F fc lo m fdw (hd (Z_to_bv 64 0) ps) (toks D))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (ntokw (toks D)) s4 (ntokw (toks D)) s6 s7 s8
               s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DISPATCH) fc None m (seg_rom rsegs)).
Proof.
  intros SCMP CSPN NCMP VIS IIV ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo D fdw ps can
    (HNE & HDL & HMSG & HTOK & HW & HIV & HINFO & HSSP & HMI & ST & LO & HIT).
  pose proof (toks_length D) as NL.
  destruct (toks D) as [|v args] eqn:TK; [congruence|].
  destruct ps as [|p0 ps']; [inversion HW|].
  assert (HW0 : cstr0_at m (bv_unsigned p0) v /\ off_lo lo sp (bv_unsigned p0) (Z.of_nat (length v + 1)))
    by (inversion HW; assumption).
  destruct HW0 as [HV OV].
  assert (VL : Z.of_nat (length v) + 1 < 2^62).
  { pose proof (toks_len D v ltac:(rewrite TK; left; reflexivity)). lia. }
  cbn [hd]. cbn [map concat] in HTOK. apply bytes_at_app in HTOK. destruct HTOK as [HT0 _].
  exact (part_a SCMP CSPN NCMP VIS IIV sp gp tp s0 s1 s9 s10 s11 F fc m lo fdw p0 v args can HV OV VL HIV HINFO HSSP
           LO HIT NL s2 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 t3 t4 t5 t6 HMSG HT0 HMI ST).
Qed.
