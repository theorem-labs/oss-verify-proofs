(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import RelSpec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma arel_page_round_up_Z_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z)|] [|@__ff; @__varmap; @__wit; @__arith; @r; @q; @H4; @H3; @H2; @H1; @H0; @__sat0; @__sat1; @__x1; @__x2; @__x3; @__p1; @H6; @H5; @__sat2; @H; @z|] "#%g#4#u#7#F#L#G#E###%#M#$#&#=#(#?#8#'#Z#;#K#Q#R#[#]#a#)#b#c#,#d#-#j#k#h#n#v#w#4#>#@#A#B#D#C#N#P#T#U#O#V#^#*#+#/#g#l#f#m#p#r#t#q#u#x#3#.#e#y#\#:#<#9#S#Y#_#`#X#W#I#H#o#J#i#s3#e%#f%#g$#h%#i&#j%#k%#l%#m%#n%#o'#p*#q+#r%#s%#t%%M%#%#%#%#%#%#%#%#%#%#%#US##$H#US#M&$#US7OUS8OUS9CUS:CUS;C0C+0CE-C$S$#.&GDDF#JZS<'GDDF#VS=(FVS>S%S&VS?HI'S%#S&m$%#WS@CEKXSAHI$#l#$*)#l#%21#l#&54#'C:Ek###SBl#'%#HWP:=#+;>,?#(=@$$#'C?#$Ks##&#BVS'#s#%#E$#Es#'$Ls#(&#s#'(#s#*#E#k##'#k##)#$Is#.&#s#-VS(#s#0#E$$Qs#2&#s#1+#s#4#E#k##1#k##(#VP1s#8USCA,s#:((*s#;$$#'C,#k##'#VR.s#?)Es#@$Ns#A&#s#@(#s#C#E#)$s#E*$#k##)#VS)(s#H)s#IE$S*s#J&#s#I(#s#L)s#M##$E*$#k##)#VS+(s#Q$SDs#R&#s#Q+#s#T'C#Ek##s#>#VS,&s#W$SEs#X&#s#W(#s#Z'C#$k##s#D#+&s#]$S-s#^&#s#](#s#`-Cs#WS.s#X.s#ZGDDF#Jl#$#s#Us#Ol#%s#^s#]#l#&s#as#`#l#'#s#(Hl#()C#l#)-C#l#*4/#l#+;6#l#,s#%=#l#-s#/s#'#l#.s#7s#1#l#/s#@s#9#l#0s#Ls#D#WRs#Ns#p#(s#Os#q#E#)$s#s*$#VS's#Hs#u#Es#=k##s#R#k##s#I#VS(s#Rs#y#Es#S+s#;s#{#E#k##s#X#k##&#VPs#Ns$#,s$$'$#s#@'Cs#B#k##s#L#VRs#Ds$(#Es#;)s#<s$**$#k##s#J#VS)s#@s$-(s#9s$.)s$/##$E*$#k##s#G#VS+s#>s$3'Cs#5Ek##s#y#VS,s#;s$6'Cs#5s#6k##s#|#+s#8s$9$S/s$:&#s$9(#s$<#EH)Hs$>*$#,Is$@#SF#j##%#)Ks$C#EI)Ls$EUS0S1US0#1C#1C%1CS1WS2C$#WS2C&#VSG#SHWSIO#s$JVS3CIVS3CLXSJC$K#USKDZSLs$KGDDFNUSMM2C#-C#S.s$M.s$OGDDF#J[SNs$PGDDF'#/s$QGDDFs#U)#2CMWS4C#s$R0Cs$ZWSOC$#2Cs$jWS5Cs$V#WS4C#--C&S$#.s$ZGDDF#J/s$[GDDFs$V3#WS5C(s$[-C-SP#.s$^GDDF#J/s$_GDDF&7#/s$`GDDF18#l#$#s$[s$Ul#%;s$c#l#&?s$f#j#1C#j#2C#j#3C#j#4S6#*Qs#-k##s$3#,s$rL$#Q'Cs$G#k##s$\#,Ls$v#I#k##%#k##*#k#1C#k#2C#k#3C#k#4S6##ENZH#NS*SQS/SRl#'3%#j#5s#>#j#.s#@#V#KHj##s#C#j##s#J#YSSs#Ks#Js#F#S-l#(s#MC#l#)s#QC#l#6s#Us#S#l#*s#Ys#W#l#+s#`s#[#l#,s#fs#b#l#-s#ls#h#l#0s#ss#n#l#7s#xs#u#l#.s#~s#z#l#8s$vs$q#USTH#H#m#%#j#9C##"). Qed.

(* [comment removed for export] *)
Lemma map_contains_false_of_free : forall maps (addr n : word),
  (0 < bv_unsigned n)%Z ->
  region_free maps addr n = true -> map_contains maps addr n = false.
Proof.
  induction maps as [|[b s] maps IH]; intros addr n Hn Hf; [reflexivity|].
  cbn [region_free] in Hf. apply andb_true_iff in Hf. destruct Hf as [H1 H2].
  unfold map_contains. cbn [existsb fst snd]. fold (map_contains maps addr n).
  rewrite (IH addr n Hn H2). rewrite orb_false_r.
  unfold iv_overlap in H1. apply negb_true_iff in H1.
  apply Bool.not_true_is_false. intros Hc. apply andb_true_iff in Hc. destruct Hc as [C1 C2].
  apply Z.leb_le in C1. apply Z.leb_le in C2.
  apply andb_false_iff in H1. destruct H1 as [D | D]; apply Z.ltb_ge in D; lia.
Qed.

Lemma region_free_app_r : forall X1 X2 (a n : word),
  region_free (X1 ++ X2) a n = true -> region_free X2 a n = true.
Proof.
  induction X1 as [|[b s] X1 IH]; intros X2 a n H; [exact H|].
  cbn in H. apply andb_true_iff in H. apply IH. tauto.
Qed.

Lemma region_free_app_l : forall X1 X2 (a n : word),
  region_free (X1 ++ X2) a n = true -> region_free X1 a n = true.
Proof.
  induction X1 as [|[b s] X1 IH]; intros X2 a n H; [reflexivity|].
  cbn in H |- *. apply andb_true_iff in H. destruct H as [H1 H2]. rewrite H1. cbn. eapply IH; exact H2.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_rw_commit_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ (mmap_fixed_rw_budget_ok flags m addr n = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
                (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next h addr n) m)) [])
  \/ (exists e, In e mmap_errnos
       /\ o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
                 (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) []).
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw. cbv zeta.
  intros Hce Hal Hpos Hrf Hmc.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf, Hmc. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right; left. split; [assumption | reflexivity].
    + right; right. eexists; split; [eassumption|reflexivity].
  - intros [(e & He & ->) | [(Hb & ->) | (e & He & ->)]].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right; left. eexists _, _, _, _. split; [exists tt; split; [exact Hb | reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
    + right; right. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.
Scheme kc__2 := Elimination for LinuxProcessSemantics.LinuxProcessSem.Monad.outcome Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Logic.ex Sort Prop.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mmap_fixed_rw_fresh_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ (mmap_noreserve_backed_ok flags m nZ = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
                (with_mmap_backing flags addr n
                   (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
                      (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) []).
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z).
  { pose proof (arel_page_round_up_Z_ge (bv_unsigned len)). pose proof (word_unsigned_range len).
    assert (bv_unsigned len <> 0%Z).
    { intros E. unfold w_is0, bv_eqb in Hlen. rewrite E in Hlen. cbn in Hlen. discriminate. }
    lia. }
  assert (Hn : (0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))%Z).
  { rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HnZ|].
    change (bv_modulus 64) with (2^64)%Z. unfold two_pow_64 in *. lia. }
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (region_free_app_l _ _ _ _ Hrf) as Hrfr.
  pose proof (map_contains_false_of_free _ _ _ Hn Hrfm) as Hmc.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrfr, Hmc, Hrf. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption | reflexivity].
  - intros [(e & He & ->) | (Hb & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists addr; split; [split; [reflexivity | exact Hb] | reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_noaccess_fresh_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] [])
            (with_mmap_backing flags addr n
               (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
                  ((addr, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z).
  { pose proof (arel_page_round_up_Z_ge (bv_unsigned len)). pose proof (word_unsigned_range len).
    assert (bv_unsigned len <> 0%Z).
    { intros E. unfold w_is0, bv_eqb in Hlen. rewrite E in Hlen. cbn in Hlen. discriminate. }
    lia. }
  assert (Hn : (0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))%Z).
  { rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HnZ|].
    change (bv_modulus 64) with (2^64)%Z. unfold two_pow_64 in *. lia. }
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (region_free_app_l _ _ _ _ Hrf) as Hrfr.
  pose proof (map_contains_false_of_free _ _ _ Hn Hrfm) as Hmc.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrfr, Hmc, Hrf. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. reflexivity.
  - intros [(e & He & ->) | ->].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists addr; split; reflexivity|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_noreplace_rw_fresh_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = false ->
  mmap_noreplace_noaccess_b prot flags off = false ->
  mmap_noreplace_rw_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ (mmap_noreserve_backed_ok flags m nZ = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
                (with_mmap_backing flags addr n
                   (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
                      (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) []).
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw Hnna Hnrw. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw, Hnna, Hnrw. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption | reflexivity].
  - intros [(e & He & ->) | (Hb & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists addr; split; [split; [reflexivity | exact Hb] | reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mmap_noreplace_noaccess_fresh_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = false ->
  mmap_noreplace_noaccess_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] [])
            (with_mmap_backing flags addr n
               (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
                  ((addr, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw Hnna. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw, Hnna. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. reflexivity.
  - intros [(e & He & ->) | ->].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists addr; split; reflexivity|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.
