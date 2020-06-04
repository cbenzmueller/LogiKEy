theory PreferenceLogicApplication1 imports PreferenceLogicBasics PreferenceLogicTests                    
begin 
(***** proof of concept formalization*****)

(*values*)
consts EFFI :: \<sigma> GAIN :: \<sigma>
consts STAB :: \<sigma> RELI :: \<sigma> 
consts WILL :: \<sigma> RESP :: \<sigma>
consts EQUI :: \<sigma> FAIR :: \<sigma>
(*TODO: encode dialectical relations between values*)

(*kinds of situations*)
consts WildAnimals :: \<sigma>  (*appropriation of wild animals*)
consts DomesticAnimals :: \<sigma> (*appropriation of domestic animals*)
(*...*)

axiomatization where
ax_1: "\<lfloor>WildAnimals \<^bold>\<rightarrow>  (STAB  \<^bold>\<preceq>\<^sub>A\<^sub>A  WILL)\<rfloor>" and
ax_2: "\<lfloor>DomesticAnimals \<^bold>\<rightarrow>  ((RELI \<^bold>\<and> WILL)  \<^bold>\<preceq>\<^sub>A\<^sub>A  STAB)\<rfloor>"
(*...*)

(*TODO: find an use to ceteris paribus preferences*)

end


