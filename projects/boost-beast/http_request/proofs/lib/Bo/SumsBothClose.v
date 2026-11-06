(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import BothImages.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec StoreOk Hoare AgentLib.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanPopFree AsanPlanSoundSums SumsBothSpecs BothIStrncpy BothPopFree BothPlanImages.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Scheme kc__1 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.False Sort Prop.

(* [comment removed for export] *)

Lemma istrncpy_clob_sub : forall r, In r istrncpy_clob -> In (AX2.ridx r) AP.caller_saved.
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BothIStrncpy.istrncpy_clob); constr:(@kc__1); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ridx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.caller_saved); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.eq_refl); constr:(@kc__2)|] [|@r; @H|] "#'7#0#H#A###@#C#%#>#$#&#'#(#)#*#+#7#,#-#4#3#9#G#.#/#J#;#?#E#F#8#B#5#=#<#I#H#D#:#61#:&#;%#<&#=$#>&#?$#@$#A$#B&#C%#D&#E)#F)#G$0P)#US##US$#'#DS%)&*#+'#H#'#I)P0#0#*#+-#H#-#I)'*#+1#H#1#I),0#*#+6#H#6#I)'*#+:#H#:#I$#E$(#$.#$3#$:#(G'C#Fj##%##s##?G(D'C#Fj#$s#&#&S&(s#$#C$#&%&#&#&##C#(&$#C#*&$#C#,&$&#&##C#0&$#C#2&$#C#4&$#C#6&$#C#8&$#C#:&$#C#<&$#C#>&$&#&#&#&#&#&#&#&#&#&##C#s#*&$#C#s#,&$#C#s#.&$#C#s#0$#E$&#$)#$,#$9#$<#$?#$B#$s#%#$s#(#$s#+#$s#.#$s#3#$s#6#$s#9#,Cs#@-s#1)#%s#4)#%s#9)#%s#<)#%s#?)#%s#E)#'Cs#GFm#$#.s#os#ks#K#JDj#%s#O#U#Dj##s#m##s#ss#iG#s#ts#fG#s#us#bG#s#vs#_G$#E$%#$'#$)##s#{s#qJ#s#|s#nJ#s#}s#jJ#s#~s#gJ$#E$%#$'#$)#(K'C#Fj##%##s$*s#|K(s#}#Cs#c##Cs#^$#Cs#]%#Cs#\&#Cs#Y'#Cs#X(#Cs#W)#Cs#V*#Cs#U+#Cs#T,#Cs#S-#Cs#R.#Cs#G/#Cs#F0#Cs#E1#Cs#D2$#E$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#,CB-<*#%>*#%@*#%B*#%s#$*#%s#&*#%s#(*#'Cs#*Fm#$#.s$Us$Ks$1#LDj#%s#.#U#Dj##s#;##s$Ys$KK#s$Zs$GK#s$[s$DK$#E$%#$'##s$_s$QL#s$`s$ML#s$as$JL$#E$%#$'#(M'C#Fj##%##s$hs$ZM(s$[#Cs$E##Cs$@$#Cs$?%#Cs$>&#Cs$;'#Cs$:(#Cs$9)#Cs$8*#Cs$7+#Cs$6,#Cs$5-#Cs$4.#Cs$)/#Cs$(0#Cs$'1#Cs$&2$#E$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#,CB-;+#%=+#%?+#%A+#%s##+#%s#%+#%s#'+#%s#)+#'Cs#+Fm#$#.s%8s%*s$p#NDj#%s#/#U#Dj##s#:##s%<s%)M#s%=s%&M$#E$%##s%@s%-N#s%As%*N$#E$%#(O'C#Fj##%##s%Gs%4O(s%5#Cs%$##Cs${$#Cs$z%#Cs$y&#Cs$v'#Cs$u(#Cs$t)#Cs$s*#Cs$r+#Cs$q,#Cs$p-#Cs$o.#Cs$d/#Cs$c0#Cs$b1#Cs$a2$#E$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#,CB-:,#%<,#%>,#%@,#%B,#%s#$,#%s#&,#%s#(,#%s#*,#'Cs#,Fm#$#.s%ts%as%P#QDj#%s#0#U#Dj##s#9##s%xs%aO$#E#s%zs%cQ$#E(R'C#Fj##%##s&#s%hR(s%i#Cs%\##Cs%W$#Cs%V%#Cs%U&#Cs%R'#Cs%Q(#Cs%P)#Cs%O*#Cs%N+#Cs%M,#Cs%L-#Cs%K.#Cs%@/#Cs%?0#Cs%>1#Cs%=2$#E$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#,CB-9-#%;-#%=-#%?-#%A-#%s##-#%s#%-#%s#'-#%s#)-#%s#+-#'Cs#-Fm#$#.s&Qs&:s&-#S'Dj#%s#1#U#Dj##s#8#(S('C#Fj##E#VS)#Dj#%E#U#Dj##E#/s#@Es#<*#Dj#%s#B#U#Dj##s#{#/s#~s#|s#xs#G#Dj#%s$$#U#Dj##s$^#/s$cs$_s$[s$+#Dj#%s$e#U#Dj##s%D#/s%Ks%Es%As$n#Dj#%s%M#U#Dj##s&O#/s&gs&Ps&Ls%X#Dj#%s&l#j#$s&n##"). Qed.

Lemma both_istrncpy_spec : APSX.istrncpy_spec BSEGS2 (AP.x_istrncpy BOTH_H) (AP.x_sealed BOTH_H).
Proof.
  intros mem0 dst regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12.
  destruct (both_istrncpy_sealed mem0 dst (seg_rom BSEGS2) regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12)
    as (regs' & Hms & Hag).
  exists regs'. split; [|split].
  - replace APSX.SEALED_BYTES with strncpy_sealed_bytes by reflexivity.
    replace (Z_to_bv 64 (AP.x_istrncpy BOTH_H)) with both_istrncpy_entry by (apply bv_eq; reflexivity). exact Hms.
  - eapply kept_ok_of_regs_agree; [apply istrncpy_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold istrncpy_clob. cbn. intros [H|[H|[H|[H|[H|[]]]]]]; discriminate.
Qed.

Lemma both_popfree_spec' : popfree_spec BSEGS2 (AP.x_popfree BOTH_H).
Proof. exact both_popfree_spec. Qed.

(* [comment removed for export] *)

Section AsanNodes.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> AP.CEIL <= bv_unsigned a.
Hypothesis argH_sp0 : forall E (a : word), argH E a = true -> bv_unsigned (AX2.edenot E AP.e_sp0_early) <= bv_unsigned a.  (* [comment removed for export] *)
Hypothesis E_SP0 : AP.expr_vars_lt nx0 AP.e_sp0_early = true.                                                                    (* [comment removed for export] *)
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.

#[local] Notation XSTMT := (APS.x_stmt BSEGS2 BOTH_H nx0 LIMIT SINV argH FS0).

#[local] Ltac close_with NODE SPEC :=
  eapply NODE; try eassumption;
  first [ exact both_wx | exact both_in_hull | exact both_res_len | exact both_hull_ok | exact both_segs_wr | exact SPEC | idtac ].

Theorem both_node_x_sound_XIMemset : XSTMT AP.XIMemset.
Proof. eapply APSX.node_x_sound_XIMemset; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_fill_spec_imemset. Qed.
Theorem both_node_x_sound_XMemset : XSTMT AP.XMemset.
Proof. eapply APSX.node_x_sound_XMemset; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_fill_spec_memset. Qed.
Theorem both_node_x_sound_XIMemcpy : XSTMT AP.XIMemcpy.
Proof. eapply APSX.node_x_sound_XIMemcpy; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_copy_spec_imemcpy. Qed.
Theorem both_node_x_sound_XMemcpy : XSTMT AP.XMemcpy.
Proof. eapply APSX.node_x_sound_XMemcpy; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_copy_spec_memcpy. Qed.
Theorem both_node_x_sound_XMemIsZero : XSTMT AP.XMemIsZero.
Proof. eapply APSX.node_x_sound_XMemIsZero; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_miz_spec. Qed.
Theorem both_node_x_sound_XIStrncpy : XSTMT AP.XIStrncpy.
Proof. eapply APSX.node_x_sound_XIStrncpy; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_istrncpy_spec. Qed.
Theorem both_node_x_sound_XPopFree : XSTMT AP.XPopFree.
Proof. eapply APSX.node_x_sound_XPopFree; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_popfree_spec'. Qed.
(* [comment removed for export] *)
Theorem both_node_fillfz_sound : forall hs ws cold fz n0 (i : bool),
  APS.fz_item_stmt BSEGS2 BOTH_H nx0 LIMIT SINV argH FS0 hs ws cold fz n0
    (fun cs => if AP.fill_in_wins hs ws cs
               then AP.summary_fill BOTH_H nx0 cs (if i then AP.x_imemset BOTH_H else AP.x_memset BOTH_H) (if i then 256 else AX2.two64) else None).
Proof. eapply APSX.node_fillfz_sound_of; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok; [apply both_fill_spec_imemset | apply both_fill_spec_memset]. Qed.
End AsanNodes.
