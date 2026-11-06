(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanHexScan AsanHexTree AsanInit BothImages BothPlanImagesHex BothPlanImagesHex2 BothPlanImagesHexZ.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition BSEGS2 : list Segment := AsanUbsan.M.loaded_segments.
Definition BPH2 : PhdrInfo := AsanUbsan.M.phdrs.

Lemma both_wx : wx_segs_nowrap BSEGS2.
Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.wx_segs_nowrap_of_b); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BothPlanImages.BSEGS2); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.wx_segs_nowrap_b)|] Array.empty "##(###*#)#*#'#(#,#+#&#VFCDUGEWHC#Dm$%#VIE##"). Qed.

(* [comment removed for export] *)
Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.

Lemma find_segment1_none_outside : forall segs lo hi x,
  segs_in_hull_b segs lo hi = true -> (x < lo \/ hi <= x) -> find_segment segs x 1 = None.
Proof.
  induction segs as [|s l IH]; intros lo hi x Hb Hx; [reflexivity|].
  cbn [segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
  - exact (IH lo hi x Hl Hx).
  - symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.

Lemma both_segs_in_hull : segs_in_hull_b BSEGS2 (img_lo BOTH_H) (img_hi BOTH_H) = true.
Proof. vm_compute. reflexivity. Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.or Sort Prop.

Lemma both_in_hull : forall a : word,
  APS.in_hull BOTH_H (bv_unsigned a) = false -> find_segment BSEGS2 (bv_unsigned a) 1 = None.
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.in_hull); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BothImages.BOTH_H); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BothPlanImages.find_segment1_none_outside); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BothPlanImages.BSEGS2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.img_lo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.img_hi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BothPlanImages.both_segs_in_hull); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.Bool.Bool.andb_false_iff); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@kc__2); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.leb_gt); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.ltb_ge); constr:(@Corelib.Init.Logic.or_intror); constr:(@Stdlib.micromega.RingMicromega.OpLe)|] [|@b2; @b1; @y; @x; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @H; @H0; @a|] "#$z#,#c#4#H#$#8###%#U#&#V#T#6#2#L#Y#X#W#[#R#`#0#/#5#;#<#B#'#I#)#*#K#M#O#P#N#Q#S#Z#\#]#_#a#b#c#^#+#J#d#f#e#E#9#:#=#3#7#1#@#C#D#F#G#?#A#>/#X&#Y%#Z$#[%#\%#]%#^%#_%#'&#`%#a%#b(%N%#%#%#%#%#US&#US'#$$GVS(M##C#FUS)MUS*M$)E,EG#C#F#CHF#CEF&$#k##&##CGF&&#,HE#C#Fk##%#-(##CJF&#-k##'#j##&#,JH#C#Fk##0#j###Ej##1#VS+EG.3.)$#j#$C#j#%C#k#$C6k#%C#$s#%H'A#($A+$#E#C%F#C%F&$#$s#,J's#(##C#F(%s#)#C#F&%#$s#2S,)#s#.*s#.$&$#j##'#'s#2'#C#F'EG#C#F)EHk##$#)GE'HE#C#Fk##%#-'#)HJk##&#j##%#'JH#C#Fk##.#j###Ej##/#VS-EG.1-)$#j#&D#j#'D#k#&D4k#'D#$s#PS.+s#L#E)$s#M$s#SS/)#s#O*s#O$US0OUS1OVS2DHUS3DXS4D$E#US5DUS6DVPDNVPDs#dXQD$S7#[R&LIIK#S#US8I\S$(LIIK$#$VS9)KVS:CS%VS;GH#C#S%m$%#WS<DS=EXS>GH$#l#(*)#l#)32#l#*87#j#+D#j#,D#k##s#4s#6k#+D#k#,D#$s#rS?+s#n#El#-(%#WS@s##B#l#.s#'s#&#l#/s#,s#*#j#.s#B#U#Gj##s#N#(s#Ks#u#C#F(EG#C#F*EHk##$#*GE(HE#C#Fk##%#-'#*HJk##&#j##%#(JH#C#Fk##.#j###Ej##/#VSAEG.1-)$#j#&D#j#'D#k#&D4k#'D#+s#Fs$2E*s$3s#GXQDs#;SBs#:[Rs#=LIIK#S#\S$s#>LIIK#s#9#l#(#s#8s#2l#)s#Bs#A#l#*s#Gs#F#j#+D#j#,D#k##?Ak#+D#k#,D#+s#1s$?El#-'$#WSCs#Qs#P#l#.21#l#/64#j#.s#,#U#Gj##s#z#ZSDs#}s#{s#us#1#Gl#.s$(s$%#l#/s$/s$-#ZSESFs$Ks$Js$ISG#j#.s$M#j#0s$Q##"). Qed.

Lemma both_res_len : APS.res_len_ok BSEGS2 BOTH_H.
Proof. vm_compute. reflexivity. Qed.

Lemma both_res_hull : Forall (fun iv => img_lo BOTH_H <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi BOTH_H) (segments_reserved BSEGS2).
Proof.
  assert (E : segments_reserved BSEGS2 = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x3e000); (Z_to_bv 64 0x4e000, Z_to_bv 64 0xcb000); (Z_to_bv 64 0x119000, Z_to_bv 64 0x8000); (Z_to_bv 64 0x121000, Z_to_bv 64 0x563000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi BOTH_H].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.
Scheme kc__3 := Elimination for Corelib.Init.Specif.sumbool Sort Prop.

(* [comment removed for export] *)
Lemma both_res_cover : img_lo BOTH_H < img_hi BOTH_H /\ forall z, img_lo BOTH_H <= z < img_hi BOTH_H ->
  exists iv, In iv (segments_reserved BSEGS2) /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  assert (E : segments_reserved BSEGS2 = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x3e000); (Z_to_bv 64 0x4e000, Z_to_bv 64 0xcb000); (Z_to_bv 64 0x119000, Z_to_bv 64 0x8000); (Z_to_bv 64 0x121000, Z_to_bv 64 0x563000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi BOTH_H]. split; [lia|]. intros z Hz.
  destruct (Z_lt_le_dec z 0x4e000);
    [exists (Z_to_bv 64 0x10000, Z_to_bv 64 0x3e000) | destruct (Z_lt_le_dec z 0x119000);
    [exists (Z_to_bv 64 0x4e000, Z_to_bv 64 0xcb000) | destruct (Z_lt_le_dec z 0x121000);
    [exists (Z_to_bv 64 0x119000, Z_to_bv 64 0x8000) | exists (Z_to_bv 64 0x121000, Z_to_bv 64 0x563000)]]];
    (split; [cbn [In]; tauto | cbn [fst snd]; rewrite !u64_lit by lia; lia]).
Qed.

Lemma both_hull_ok : APS.hull_ok BOTH_H.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi BOTH_H]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma both_shadow_ok : APS.shadow_ok BOTH_H.
Proof. unfold APS.shadow_ok. cbn [shadow_off BOTH_H]. lia. Qed.

Lemma both_res_sizes : APS.sum_sizes (segments_reserved BSEGS2) = 0x674000.
Proof. vm_compute. reflexivity. Qed.

Lemma both_segs_wr : APSX.segs_wr_ok BSEGS2.
Proof. intros seg Hin Hw. cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hw |- *; congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma both_hex3_pt : forall i, (i < 5648384)%N -> hex_byte_at AsanUbsan_seg_bytes_003 i <> None.
Proof.
  intros i Hi.
  destruct (N.lt_ge_cases i 55744) as [H1|H1]; [exact (both_hex3a i H1)|].
  destruct (N.lt_ge_cases i 584176) as [H2|H2].
  { replace i with (55744 + (i - 55744))%N by lia. apply (zpt_vpt _ _ _ both_ia_zero). lia. }
  destruct (N.lt_ge_cases i 976536) as [H3|H3].
  { replace i with (584176 + (i - 584176))%N by lia. apply both_hex3b. lia. }
  destruct (N.lt_ge_cases i 5170840) as [H4|H4].
  { replace i with (976536 + (i - 976536))%N by lia. apply (zpt_vpt _ _ _ both_tab_zero). lia. }
  replace i with (5170840 + (i - 5170840))%N by lia. apply both_hex3c. lia.
Qed.

Lemma both_segs_eq : BSEGS2 = [AsanUbsan_segment_000; AsanUbsan_segment_001;
                              AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.

Lemma both_rw_window : forall m (x : word),
  0x119000 <= bv_unsigned x < 0x684000 -> wview BSEGS2 m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment BSEGS2 (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite both_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           AsanUbsan_segment_000 AsanUbsan_segment_001
           AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some_pt _ 32768); [exact both_hex2 | rewrite both_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some_pt _ 5648384); [exact both_hex3_pt | rewrite both_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x121000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma both_img_facts : img_facts BSEGS2 BOTH_H BPH2.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi BOTH_H]. lia.
  - vm_compute. reflexivity.
  - exact both_res_hull.
  - rewrite both_res_sizes. reflexivity.
  - cbn [rw_lo rw_len BOTH_H]. split; [lia|]. intros m x Hx. apply both_rw_window. lia.
  - exact both_shadow_ok.
Qed.

(* [comment removed for export] *)
Lemma itab_ranges_ok : forall rs, itab_sound BSEGS2 (mk_itab_ranges BSEGS2 rs).
Proof. intros rs. apply APS.mk_itab_ranges_sound. Qed.
