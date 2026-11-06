(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn11w2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.A3Dict.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition KNX1 : list kentry := vr_entries VR_A3 ++ tr_kn D_A3 VR_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.KN_MAIN.
Lemma KNX1_eq : vr_entries VR_A3 ++ tr_kn D_A3 VR_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.KN_MAIN = KNX1.
Proof. vm_cast_no_check (eq_refl KNX1). Qed.
Definition KNX2 : list kentry := vr_entries VR_A3 ++ tr_kn D_A3 VR_A3 A3.BootKn11w2.KN_MAIN.
Lemma KNX2_eq : vr_entries VR_A3 ++ tr_kn D_A3 VR_A3 A3.BootKn11w2.KN_MAIN = KNX2.
Proof. vm_cast_no_check (eq_refl KNX2). Qed.

(* [comment removed for export] *)
Definition DROP1 : list kentry := tr_dropped D_A3 VR_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.KN_MAIN.
Definition DROP2 : list kentry := tr_dropped D_A3 VR_A3 A3.BootKn11w2.KN_MAIN.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn10b__B3.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.A3Dict.TwB.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition KNX1 : list kentry := vr_entries VR_A3 ++ tr_kn D_A3 VR_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.KN_MAIN.
Lemma KNX1_eq : vr_entries VR_A3 ++ tr_kn D_A3 VR_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.KN_MAIN = KNX1.
Proof. vm_cast_no_check (eq_refl KNX1). Qed.
Definition KNX2 : list kentry := vr_entries VR_A3 ++ tr_kn D_A3 VR_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w2.KN_MAIN.
Lemma KNX2_eq : vr_entries VR_A3 ++ tr_kn D_A3 VR_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w2.KN_MAIN = KNX2.
Proof. vm_cast_no_check (eq_refl KNX2). Qed.

(* [comment removed for export] *)
Definition DROP1 : list kentry := tr_dropped D_A3 VR_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.KN_MAIN.
Definition DROP2 : list kentry := tr_dropped D_A3 VR_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w2.KN_MAIN.
End TwB.
