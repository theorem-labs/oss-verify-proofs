(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the launch's channel reader. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts
  MmapSim AllocSim FileSim AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame
  Spec LibWritev RefExitBase RefStdioDefs RefExit LibStdioCall RefMemcpyLib RefMemcpyBase RefMemcpy RefMemchr RefStrnlen
  LibTail.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import RefOpenFailCS_defs RefOpenFailCS_tail.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefOpenFailCS_tail2 () := KReplay.lz_vm "#%g3C47Corelib7Program6Basics4flipC46Stdlib5Lists4!s+#8nil_cons!sa,4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?!s<22Fs2F!sr-!t8%7!s+#Def3map!t686!t6%!to8map!to&!sC5:firstn_nilK!uq,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!u419Datatypes4list00!tTG1!vk;5Riscv7Prelude5bvmap!t?<6op!te#00C!sH<lengthK!sF;3nat!uk#!wV62eq00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun7vals_evC13~~~!shPBRefOpenFailCS_tail3ENV!sp&8!spN=SymExec2Sound4SX2S7regs_ok!stjknow!st,!yM@;bv_unsignedC5!{%&6ZArith6BinInt1Z2leK!tbO8!tb'3SX24expr02!t[%!{H>Z03!t3c1!t3F2K!|2A1!tS]5sadd!tT,!sn\6sentry!soe!v4%4!t^dk!t^%6!sok1!sok5!sok7!sok!w3d9sym_state!vEe7scripts!sp'!#5GO8Prop!sq#7seg_rom!sjV4Spec9exit_code!#4?&!#=CH5S!u|#4m_fs!u/QShapeAlg6t_!tI#!tD%!#;a<prod!#;a-!sF81K!#:#:1C!wf\8!xZ#exec!v7&!#4$]_log!sldcarry!slV!#9z58sc_deno!wD&K!#BQ96Forall!vc_6s_regs!u,i9mem!u-/!#<'@7Z_to_bv!|fY4mks!v=+!{yI3Run6config01!}@U1W!uLG6bv_and!}&]mi!v\+!#G:49nth_error!t/P9SymDriveX8!#@l#nth!x`j!#7_$!#Ae,!#4LN8m_haltedK!#G/B2!t#Q9m_vm_lazy!vEP;RefExitBase:file_clean!#5Y7!#4q&x!#JV3!s@%3and00I!tMO<RefStdioDefs>stdout_pending00!w#W5m_fds!vZRfd_lookupK!s^P7FdE!#@-$!vH9or00!#GJ;3sub!#4s\2!#KZ&K!#OKC!#6%_r_get!#8vb6e!#5x-!sm]a!sm/!vv<add!#30Y>!tv%_add_l!#4B'!#7RXgetr!sgV!#Q-&reg_val!ubB6of_nat!sF34Znat5Nat2Z7inj_iff!#WM77iff_sym!#6u'9micromega;ZifyClasses7rew!sj$!t5=9is_nonnegK!sr56VarMap1!#TL#!sD>0!sD6=RingM!s4'7Formula00!t567Env!sT#5PE!#PO#!sIE4!uo65Tauto8B!t8&!sH6:Z!t^+=Z!sT$CheckerC!uS<4f!#[T-!sq8C!sq0_soun!#Sf<>pow_po!w:'!#T6=t!|6=pow!sC<:!t/#!x?<!ve21!sIE7!#WIcu_small!#8aP>!#\p#!sE+8store_ok!zc@1!#aq8!|:#refl!|;B3inj!sIB;!|^&_rev!#4XY<kwr_!uD'!#8W&!|KK1!#Uwb7!#>]8Peano2le00!uwB9and_morph!y,c4fla!#9Nc7ext!#6k,!#<??C!#I8%_!#^E,K!#3L;G!w9'3!#8SV=!tf&_zx_id!{``@word!u0#le_bytes!#]kA2!#EuC1K!#Cn[;!#U6%mm!sn#!z|'!#EA9!#SN8!#EA#!#Si9or!#LYQ7!#G&%:ref!#UW#_Z!xyG5bv_eq!#LdX4t!sa#!#>]T!ty'?!#ML$_nil!#WY,!tZY8!tZ#!#>E#!wP%!skYrealizes03!}Ec4s_p!#X/%I!tZb!#J`%!#5Fb3!t\V!{X=0!v?c6a_base!smc5a_off!{P'!#7W?5mkrel!#5>E4!sJF8!sJF5!t_Eapp!sKB6!sK$!#D6E3!#IZX3rdn!}/X!#=\%5kread!wGH!#yG#ff!t6Y9!t6$_!t|Y!#?Z+;!#N=$_lit0!um_6rz_run!#8F&!#y2>5Instr5aluop01I!}}b!u+&I!#Rm]!#kz$!soek!so0!#t-?!#VZ,!sD6!#}X<!#{U#0!#LP;5eKind!#i[<unit!#M}7!se%4ki!#<p$!#EKA3Op203K!t5A1!tU=bool!#k2>!sF$!tUJ5!zn/!wp96images5Plain1M?loaded_segment!#gZ&!#Rf<6inj_le!|#P4Scfg=hunspell_scfg!|mV!$#U1defs4FUEL!sqi5STOPS!tejscr0!tejsrI3!srkkn!sr+!}G=!$-u+!{;=!}0$!#4\]8sidecond!#3od!#xk,!srd!#xk'!sp'!#dZX0!#I+74True!~g#!~#4!#Xr,;!|~%!u+$!#hR9!sn%!#5M68ZifyInst7Inj_Z_Z!#3;H1!#4&A2!#7E=N!ts#!#i3Oeven!#6u#!s\V2!$5P;3!#Ab#!sC;fst!#GGb!$&5c!{Y,!$#`V<Lib!#H:#Call:s!s0#_c!#[s+!sq\6sc_ret!smc4sc_f!skc5!sk#d!slgwb!slhp!v5gs!skg!xVW!#Ed'8blob!$=9,!#3[67f_equal!$DB;trans!{d]3env!$0A`5v_ad!y4W7LibTail7vadd_wZ!si^6ed_var!shb!#q-X!sh/!v#+!#[e;2!{aas!{a'!#L&?3Sem5alu64!xAY7alu!xCZ9!#XX#Laws>!$4@$_has_ni!|7`9junk_vals!|883Nat!#vy]@!t++_!$Hu$!t3'!#=:%!$LS-!sG%_!#:s4!#hP&t!tSZ=!$H|%!t%#!#3\&c!sqOC!$I&428of_segI3!#5Ab!z9$r!slgkn!slc@!#<S+!#tY%!sw%!#5YN3Lib2Nd:and_elimF7!yo8!#@8,s!$3'Q!#KC7rH!wPW!sq7kn!sq+!#OxBt!t;c5!u-#!#LXl!srl3rG3!#6l&!#ZhD;branch_!#Cp#6!#[BGmulop!#l?Q!tv62PX!tu%I!{Z\9!{Z%r!#g~+!zKfG!zKm!sqlsc!sqk3!|{mscH!tclI!splF4!{cZ4!yRf!tK'!yRf!sqlsc!sqk3rG!splH!uUl!sqmkn!tdmcH!vIlI!spj?itinerary_63_6!s|W!$Ja#?msg_cannot_ope!#q#W!#M<,mu!$;ZB3mul!#s9D5!sf=ltb!$iHH6bv_ltu!uBP!#LW'ltu_Z!#Nm^!#OX$!sibmul!sia6ed!wZ-!#MgC<!#6B%taken!$U:B2!wj=opp!xRE6!uHP:!#Je&H46win!$OF+!skZ9log_out_!#ZM%!$9j?3!t4[Ardn_!$W&'!t>#!u+V!#MX+:flat_intro!y'^9!tc#app_Z!t[`8kimg!#{=+!x_>3P!#sLG5Psatz!$DH7!sO84!sOK6K!#inL2!#QHjH!$0xV!#Ns3!sk'!#TW59!x1#assoc!#9C^!u%#4atG!$T|'!#kU:negb!~P+5!vP$8!#Ug#Na!#WD+!$LXA!#WgR!tz69PRE17_l!#:IW!#<755sc!#JDlsrG!#L&jknG!#v+'!$'JK2!tEc6BUF_LO!u:i!ss$HI!ssi3I!spg!yX#5!yX$!sri;!zL%words!sxi6nl_img!#6R;!#4f:1!$AD@D!$G?&obliga!s:#_!$M`9!#kT%2!|herI4!#~|m!sr'!#aik4!#7G\;!#7G'!y`g!vL&H!vLnH!vLl7NL!{F$!tiV!#J8'9u64_rang!$AL&!$^p;ltb_lt!zW85proj2!#IrNs!{zA9bv_!%/PA:!t^#ir!$VW#!upO!#D1,!$c<,w0_!#h/V!ss-<!ss&exts!z}'!#Hu:!%9c$!#m^6sub!#?7;nil_r!#=~?!sd#!sF>8sub_diag!#ms7!%;H%all!sE@!#n:-7!$BC%?Rel!#4g#!s6&>eq_equivalence!sWE?E!sT,_PER!sX59Morphisms:respectful!t#E<eq_Reflexive!s|?Jr!sL'_eq_dom_r!s]GI!s],!s0,proxy!tjISymmetric!sUE8s!sR%y!t^?@!tT0per!sS?N!#}T#_sym_co_inv_impl!$\N$ism!{pP7SeqExec:rdn_!{F&!|^U!#wf0m!#wf3!#4K;to!$l=6!#X%,ax!sC<8max_!yi#!$ToO=RefMemcpyBase3mcH!$$W&I!smb!#If'!#5x>4BvW!$LDP5Hoare;ret_ok_ev!#HuW9!t}+!$[:#m!s1$!snV7Cat!yE#6w!$_;#!vWV6CatSim6mstep!#nWX<!uC+Lib5keep!#DXV!$bR%:sr_vars_l!#VG`@!%E7#after_!ta[!$$I'?sr!sq&!#zO#j!#:62!#=Z,6!$]a%!u+Z!%+Y#!t9%!$j|#!vg^kn!vgh<en!$$^$!ti#!sp%!#V?k4!w[X!$_L%9rz_!zt%!sl&!#Fd`2!tZWAgentLib:!#6e%ap!$1Q'!#>:47map!sH#!$\mE6!$Dn>@!$|c$_!#7S$!$g%R!#Hh8G!#Hhm!srmsc!#tRlsrF!$$AjknE!tcj!vK#!sqV!#6p/;callee_kep!~Ha?!so-_no0!|eV!$Hi0ridx!{u=2In!#6@73no!#?h<;le_gt_cases!wD_tail7!#44$F!#5'p!#_Qf!#Yo#!tl&_g!#?H&!tpd9!sy&!#{^f!#e+%!|bg!sq#!v[&BC!suV!#x5#5t_die!#32kB!#cll!sq'".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~k1floaded_segments37Corelib4Init5Logico92eq69OSSVerify6Proofsaboost_jsonafuzz_parse3libh2RefOpenFailCS_tail~~~~~~q23ENV37Corelib4Init9Datatypesue6lengthue4listue3natue6option3h5LinuxProcessSemanticsfLinuxProcessSem3Runhi55mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statehla4m_fs3h5LinuxProcessSemantics5Riscv7Preludehp05bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hrf4mksthrf7seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3libh2RefOpenFailCS_defs~~~~~~igd5knI30igd5srI3069OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~im5dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~iqd8realizesiqd6t_exit69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~ive9exit_code79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~jk27know_okjk27regs_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~jpd7vals_evhf7Z_to_bvigd5knH30igd5srH3001Zq24atG0iqd6t_emitive1Wivefmsg_cannot_open46Stdlib6ZArith6BinInt1Zki96of_natue4consue3nil3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticskl8h0word_to_le_bytesigd5knI40igd5srI40igd5knH40igd5srH40ki93addki92lehfbbv_unsignedue4Someue3appo93and37Corelib4Init3Natkv63addhrf3rdnigd3knEigd4srF0o93notigd4knB0igd4srB0ive5t_die36Stdlib5Lists4Listlk42Inhla5Modelhi58valid_spue4Nonehla8m_haltedue4prodhla9m_vm_lazyhla7FdEntryhla9FdChannelhla9fd_lookuphla5m_fds" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* LPS 75d69e00: ref_exit_Z takes the launch's channel reader as a separate premise, so
   the tactic takes the hypothesis that carries it. *)
Ltac close_exit HR HK P0 Hh Hlazy Hrdr sp0 :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z; [| exact Hrdr];
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x10b6b8), (bv_unsigned (ev E 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | cbn [ev ENV] in Ktid |- *; lia
      | lit_u; change (1095352 - 168)%Z with 0x10b610%Z;
        let Htc := fresh "Htc" in
        krd HK 0x10b610%Z 4%nat Htc; rewrite Htc; cbn [ev ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.

Section Tail2.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variable BL : ltac2:(zQ "30!hgf!h9!jc@1$0@1$0@1$2@1$1#8").
  Variable model : ltac2:(zQ "10!lld$0").
  Hypothesis Hvsp : ltac2:(zQ "10!lm6@1$0?3sp0").
  Hypothesis Hh : ltac2:(zQ "60!h9!jc!ln2!hhc!pd!ln9@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!h9!jc!lo5!hgf!kl2!pd!loc&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd2 : ltac2:(zQ "90!h9!lp9!ju1!ku3!hhc!pd!lq4!lr1!lre@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+2@2$3$1@1$6@2$2@1$0#k0+2").
  (* LPS 75d69e00: the stderr writes and the exit flush need the launch's channel
     reader (stdio_call_sound / ref_exit_Z premise), constant over the run. *)
  Hypothesis Hrdr : m_channel_reader model = true.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma of_segI3 : ltac2:(zQ "h80!h9!jc!n7!pd!u8!hg6!hgf!hh6!hhc!hl1!ho8!hr6!hva!ig2!il3!ilc!ipc!iu8!iv4!jj5!jo7!jp2!jt6!ju1>4vals@1$6@1$1@1$0#k0>1R@2$b@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$8@1$1@1$0#8>0@3$3$7@2$5@1$1@1$0#k0^3Nhg7>0@3$3@1$1@1$0#k0@2$h6^4N0?3sp0>0@3$h5@2$4?2BL^5$f^4>0@4$h4$2@2$4?2BL^6^4$e@4$h1$2$h0@2$9@5$c?2fx^6@2$h7@1$0#k0+ugmuc^5@1$d$2?5model@2$h2@1$h3+2@1$a?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    close_exit HR HK P0 Hh Hlazy Hrdr sp0.
  Qed.

  Lemma of_segH3 : ltac2:(zQ "h80!h9!jc!n7!pd!u8!hg6!hgf!hh6!hhc!hl1!ho8!hr6!hva!ig2!jub!jv4!ipc!iu8!iv4!jj5!jo7!jp2!jt6!ju1>4vals@1$6@1$1@1$0#k0>1R@2$b@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$8@1$1@1$0#8>0@3$3$7@2$5@1$1@1$0#k0^3Nu7>0@3$3@1$1@1$0#k0@2$h6^4N0?3sp0>0@3$h5@2$4?2BL^5$f^4>0@4$h4$2@2$4?2BL^6^4$e@4$h1$2$h0@2$9@5$c?2fx^6@2$h7@1$0#k0+ugorc^5@1$d$2?5model@2$h2@1$h3+2@1$a?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 231%nat.
    apply (rz_conseq RSEGS _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ [])) (t_exit (exit_code 2) (m_fs model)))).
    2:{ cbn [map app]. apply t_eq_sym. apply t_emit_nil_exit. }
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH3 knH3 Rc Mc model scH3 [] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH3 knH3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH3 length Z.of_nat] end.
    - lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - lia.
    - cbn [edenot]. apply u_small. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - reflexivity.
    - reflexivity.
    - exact Hfd2.
    - exact Hrdr.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (of_segI3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  Lemma of_segG3 : ltac2:(zQ "e0!h9!jc!hg6!hgf!pd!jvd!ho8!kg0!kg7!iv4!kh1!jj5!kh6!kk1>4path@1$3@1$1@1$0#8>0@3$4$5@1$d@2$2@1$1@1$0#8^1+jf@7$7?2fx?3sp0?2BL?5model^2+jf@2$8@2$a+2@1$c^2@2$9@1$b+2@1$6?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros path HP vals R M HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG3 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * 63 + 63)%Z with 0%Z by lia.
      rewrite ltu_ZZ by lia. reflexivity. }
    assert (WOK : win_ok (ENV BL vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
    rewrite P0 in Hw0, Hw1, Hw2.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
    { rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }
    assert (B80 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (17 + length path) = Some (PRE17 ++ path)).
    { apply rdn_app_Z; [exact H17 | | lia | lia].
      replace (bv_unsigned sp0 + -560 + Z.of_nat 17)%Z with (bv_unsigned sp0 - 543)%Z by lia. exact SBp'. }
    assert (Hnl : rdn RSEGS M' (Z_to_bv 64 0x13241) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knG3 ltac:(let i := kidx knG3 (is_kimg_cov 0x13241 1) in exact i)
                 _ _ 0x13241 1 HK eq_refl) by (cbn; lia). apply nl_img. }
    (* [comment removed for export] *)
    unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W.
    pose proof itinerary_63_64 as (_ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srG3 knG3 Rc Mc model scG3 (PRE17 ++ path) [Z_to_bv 8 10]
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG3 knG3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scG3];
      rewrite ?length_app, ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot length]. apply u_small. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
      replace (17 + length path)%nat with (17 + length path)%nat by lia. exact B80.
    - cbn [edenot]. exact Hnl.
    - exact Hfd2.
    - exact Hrdr.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (of_segH3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma NL_word : ltac2:(zQ "80!h9!jc!ju1!kkb!hgf!kl2!pd!kof@3$6@1$4@1$1@1$0#8@2$7N1@2$2@1$0#k0+a@3$3@1$1@1$0#8@2$2@1$0#8+a@1$5@1$1@1$0#8").
Proof.
ltac2:(KReplay.run1 (kr_t_RefOpenFailCS_tail2 ()) ["Tail2"] "h02b1h12b2h21nh31Hp;1p;2p;3p;:g003kj10Tg004Pj14Tg004nj12Tg005Qj17Tg01MJj1Bj3?Tg0061j1=Tg00AWj1<Tg03o=j2;Tg00lSj3:Tg00B5j18Tg008cj31Tg00=ej23Tg01Qoj39Tg00Rlj26Tg0400l:ATg008Dj1@Tg00Zbj25Tg01LBj2>Tg029h#0R0#0#0R1#4R2#2R3%73R4P4%B3%=0#0#<R01;205:2R5P5%83R6P6g02BTR7f0R8#2R9f1R:#2R;g00fIf2R<#2?1:8g01l5R=f3R>/3<13>:31R?[13<:13<851=%2>?1<:[R@f4#2?1><\?A9<:8P8n2001000000120000000W1W0W2P@^1;^09^27P8P2P5P51325,6=O4b31646M:Ag02:M#@%01#0#0#4/50'>1520=?36514do"). Qed.

  Lemma of_segI4 : ltac2:(zQ "h80!h9!jc!n7!pd!u8!hg6!hgf!hh6!hhc!hl1!ho8!hr6!hva!ig2!kq4!kqd!ipc!iu8!iv4!jj5!jo7!jp2!jt6!ju1>4vals@1$6@1$1@1$0#k0>1R@2$b@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$8@1$1@1$0#8>0@3$3$7@2$5@1$1@1$0#k0^3Nhg7>0@3$3@1$1@1$0#k0@2$h6^4N0?3sp0>0@3$h5@2$4?2BL^5$f^4>0@4$h4$2@2$4?2BL^6^4$e@4$h1$2$h0@2$9@5$c?2fx^6@2$h7@1$0#k0+ugmuc^5@1$d$2?5model@2$h2@1$h3+2@1$a?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    close_exit HR HK P0 Hh Hlazy Hrdr sp0.
  Qed.

  Lemma of_segH4 : ltac2:(zQ "hc0!h9!jc!n7!pd!u8!ju1!kkb!hg6!hgf!hh6!kl2!hhc!hl1!ho8!hr6!hva!ig2!kr6!krf!ipc!iu8!kg7!iv4!kh1!jj5!jo7!jp2!jt6>4vals@1$8@1$1@1$0#k0>1R@2$e@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$b@1$1@1$0#8>0@3$3$9@2$7@1$1@1$0#k0^3Nu7>0@3$3@1$1@1$0#k0@2$hb^4N0?3sp0>0@3$ha@2$4?2BL^5$h2^4>0@4$h9$2@2$4?2BL^6^4$h1@4$h4$2$h3@2$c@5$f?2fx^6@2$5@1$0#k0+ugihc^5@1$h0$2?5model@2$h5@2$h7+2@3$6@1$1@1$0#8@2$5@1$0#8+a@1$a@1$1@1$0#8@2$h6@1$h8+2@1$d?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 231%nat.
    krdv HK 0%nat (-560)%Z 1%nat Hb. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    rewrite NL_word in Hb.
    unfold adenot, v_addi in Hb. cbn [a_base a_off edenot ev ENV] in Hb. rewrite P0 in Hb.
    replace (W 2 [Z_to_bv 8 10]) with (map (WriteEv (Z_to_bv 64 2)) ([Z_to_bv 8 10] ++ [])) by reflexivity.
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH4 knH4 Rc Mc model scH4 [Z_to_bv 8 10] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH4 knH4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH4 length Z.of_nat] end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. apply u_small. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hb.
    - reflexivity.
    - exact Hfd2.
    - exact Hrdr.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (of_segI4 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  Lemma of_segFG4 : ltac2:(zQ "i70!h9!jc!pd!ks8!ksf!kt5!hgf!n7!hg6!jt6!ju1!hhc!jvd!u8!ku3!kua!kkb!hh6!kl2!kv0!lg8!hl1!ho8!hr6!hva!lgf!ig2!lh6!lhd!ipc!iu8!kg7!iv4!kh1!jj5!kh6!jo7!jp2!kk1>4path@1$6@1$1@1$0#8>2pp@1$1@1$0#k0>1P$c>4vals@1$6@1$1@1$0#k0>1R@2$h7@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$b@1$1@1$0#8>0@3$2$c@1$i6@2$8@1$1@1$0#8^6^4>0@2$h3@2$4+k0^5@2$4^5+hvvvf>0@3$2$h1@2$8@1$1@1$0#k0^5Nq7>0@3$2@1$1@1$0#k0@2$9^6N0?3sp0>0@3$2@1$1@1$0#k0@2$9^7N2^9>0@3$2@1$1@1$0#k0@2$9^8Nn1@2$a@1$0#k0^9>0@2$4@2$5@1$0#k0?3sp0@2$5@1$0#k0^b>0@2$4@2$3@2$3@2$5@1$0#k0^c^b+8@2$3@2$5@1$0#k0?3sp0+kgggg0>0@2$4@2$3@2$3@2$5@1$0#k0^d^c+8+ogggggggggg0>0@3$i5@2$d?2BL^c$hc^b>0@4$i4$7@2$d?2BL^d^b$hb>0@3$2@1$b@1$6@1$1@1$0#8@4$h9$7^c^h0@2$h4@2$8@1$1@1$0#8^h1N1@2$e@1$6@1$1@1$0#8@3$f@1$1@1$0#8^h1@3$h0@1$1@1$0#8@2$a@1$0#8Z@1$h2@1$1@1$0#8@4$he$7$hd@2$h5@5$h8?2fx^e@2$a@1$0#k0+ugihc^d@1$ha$7?5model@2$hf@2$i1+2@1$i3^h2@2$i0@1$i2+2@1$h6?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 Hpp3 HR HK Hstr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (Psmall : (bv_unsigned (edenot (ENV BL vals) (EVar 113)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P113, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep scrF4 167%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
      rewrite ltu_ZZ by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV BL vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
    rewrite P0 in Hw0, Hw1, Hw2.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
    { rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 2 (PRE17 ++ path)) (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))))).
    2:{ unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W. rewrite (map_app _ (PRE17 ++ path)).
        apply t_eq_sym. apply t_emit_app. }
    unfold W at 1.
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srF4 knF4 Rc Mc model scF4 PRE17 path
             (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))) HR HK
             (eq_trans (f_equal (fun n => stdio_call n srF4 knF4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scF4];
      rewrite ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P113. rewrite u_small by lia. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - right. cbn [edenot ev ENV PX]. rewrite P2. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P2, P113. rewrite u_small by lia. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact H17.
    - cbn [edenot ev ENV PX]. rewrite P2. exact Hsrc.
    - exact Hfd2.
    - exact Hrdr.
    - exact Hh.
    - exact Hlazy.
    - apply t_emit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R1 M1 HR HK.
      clear Hstr' Hsrc Hw0 Hw1 Hw2 H17 Psmall.
      lazymatch type of HK with know_ok _ _ _ ?k => change k with knG40 in HK end.
      lazymatch type of HR with regs_ok _ ?sr _ => change sr with srG40 in HR end.
      set (vals0 := vals) in P2, P113.
      set (vals1 := vals ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals1 vals0. clear HL P0 WOKS. clear vals. rename HL1 into HL. rename Q0 into P0.
      change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
      run_blk scr0 199%nat.
      lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ => rename Mc into MG end.
      (* [comment removed for export] *)
      set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
      assert (Hnl : rdn RSEGS MG (Z_to_bv 64 0x13241) 1 = Some [Z_to_bv 8 10]).
      { rewrite (kimg_rdn RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kimg_cov 0x13241 1) in exact i)
                   _ _ 0x13241 1 HK eq_refl) by (cbn; lia). apply nl_img. }
      assert (Hdst : store_ok RSEGS MG dst 1 = true).
      { pose proof (kwr_store_ok RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kwr_cov (EVar 0) (-560) 1) in exact i)
                      _ _ _ (-560) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
      assert (MC : mcH MG dst (Z_to_bv 64 0x13241) 1 [Z_to_bv 8 10]).
      { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
        - exact Hnl.
        - exact Hdst. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (A1 : getr Rc 1 = (0xe021c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
        assert (A10 : getr Rc 10 = dst)
          by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
        assert (A11 : getr Rc 11 = Z_to_bv 64 0x13241) by (regv HR (11 : reg); reflexivity);
        assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
        destruct (ref_memcpy MG dst (Z_to_bv 64 0x13241) 1 _ (seg_rom RSEGS) MC Rc (0xe021c : word)
                    ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
        clear A1 A10 A11 A12
      end.
      replace (Z_to_bv 64 961960) with (0xeada8 : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
      replace (0xe021c : word) with (Z_to_bv 64 0xe021c) by (apply bv_eq; reflexivity).
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R2 callee_kept
                      ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
      rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
      (* [comment removed for export] *)
      pose proof (know_after_store RSEGS (ENV BL vals1) MG knG4 (SA (EVar 0) (-560)) 1 (ELit 10) [Z_to_bv 8 10]
                    knH40 [] [] ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                    ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia)
                    ltac:(cbn [edenot]; symmetry; apply NL_word)) as HK2.
      clear HK.
      assert (Edst : adenot (ENV BL vals1) (SA (EVar 0) (-560)) = dst).
      { unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. subst dst. f_equal; lia. }
      rewrite Edst in HK2.
      pose proof (env_app_know RSEGS vals1 (junk_vals R2) (blobs_ev BL) (wbytes MG dst [Z_to_bv 8 10]) knH40
                    ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
      clear HK2.
      set (vals2 := vals1 ++ junk_vals R2) in *.
      assert (HL2 : length vals2 = 231%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV BL vals2) in HR, HK.
      eapply (of_segH4 vals2); [exact HL2 | exact Q0 | exact HR | exact HK].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem of_tail : ltac2:(zQ "i40!h9!jc!hgf!hg6!ks8!kt5!pd!n7!ksf!kk1!ju1!hhc!ku3!lgf!u8!jt6!kua!kkb!hh6!kl2!li5!lg8!hl1!ho8!hr6!hva!ig2!lib!lj3!ipc!iu8!kh6!ljb!jo7!jp2!ll7>4path@1$2@1$1@1$0#8>2pp@1$1@1$0#k0>2t8@1$2@1$1@1$0#8>4vals@1$2@1$1@1$0#k0>1R@2$h8@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$b@1$1@1$0#8>0@1$h4@3$i3@1$1@1$0#8@2$a@1$0#8Z^6>0@2$8@1$9@2$3@1$1@1$0#8^7+hvvvf>0@3$6$h2@2$3@1$1@1$0#k0^5Ni7>0@3$6@1$1@1$0#k0@2$f^6N0?3sp0>0@3$6@1$1@1$0#k0@2$f^7N2^9>0@2$8@2$5@1$0#k0?3sp0@2$5@1$0#k0^a>0@2$8@2$4@2$4@2$5@1$0#k0^b@1$9@2$3@1$1@1$0#8^c+8@2$4@2$5@1$0#k0?3sp0+kgggg0>0@2$8@2$4@2$4@2$5@1$0#k0^c@1$9@2$3@1$1@1$0#8^d+8+ogggggggggg0>0@3$i2@2$e?2BL^b$hc^a>0@4$i1$7@2$e?2BL^c^a$hb>0@3$6@1$b@1$2@1$1@1$0#8@4$d$7^b^f@2$h5@2$3@1$1@1$0#8^h0N1@2$c@1$2@1$1@1$0#8@3$h0@1$1@1$0#8^h0@3$h1@1$1@1$0#8@2$a@1$0#8Z@1$h3@1$1@1$0#8>0@3$6@1$b@1$2@1$1@1$0#8@4$d$7^c@2$a@1$0#k0@2$4@2$5@1$0#k0^h0@1$9@2$3@1$1@1$0#8^h1N8@2$c@1$2@1$1@1$0#8^f@4$he$7$hd@2$h6@5$h9?2fx^e@2$a@1$0#k0+knmm0^d@1$ha$7?5model@2$i0@1$hf^h2@1$h7?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros path pp t8 vals R M Hnonul HPl HL P0 P2 Hpp1 Hpp2 Hpp3 HR HK Hstr Ht8.
    unfold t_die.
    eapply (of_segBC sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
      try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
    destruct (Z.le_gt_cases (Z.of_nat (length path)) 62) as [Hle | Hgt].
    - eapply (of_segF sp0 BL model Hvsp Hh Hlazy Hfd2 Hrdr path pp _ vals'); try eassumption; lia.
    - destruct (Z.le_gt_cases (Z.of_nat (length path)) 63) as [Hle2 | Hgt2].
      + assert (E63 : Z.of_nat (length path) = 63%Z) by lia. rewrite E63 in Q113.
        eapply (of_segF_gen sp0 BL model Hvsp Hh Hlazy path pp 63 _ vals'); try eassumption; try lia.
        apply of_segG3. exact E63.
      + eapply (of_segFG4 path pp _ vals'); try eassumption; lia.
  Qed.

End Tail2.
