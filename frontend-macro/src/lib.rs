use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};


#[proc_macro_derive(Flatten)]
pub fn derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let iden = &ast.ident;

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();
    
    let fields = if let syn::Data::Struct(syn::DataStruct {
        fields: syn::Fields::Named(syn::FieldsNamed { ref named, .. }),
        ..
    }) = ast.data
    {
        named
    } else {
        unimplemented!();
    };

    
    let builder_fields = fields.iter().map(|f| {
        let name = &f.ident;
        quote! { value.#name }
    });

    let vec_to_fields = fields.iter().enumerate().map(|(id, f)| {
        let name = &f.ident;
        quote! {#name: vec[#id]}
    });

    let state_number = fields.len();

    let expanded = quote! {
        
        impl #impl_generics #iden #ty_generics #where_clause {
            pub fn state_number() -> usize {
                #state_number
            }
        }

        impl #impl_generics From<#iden #ty_generics> for Vec #ty_generics #where_clause {
            fn from(value: #iden #ty_generics) -> Vec #ty_generics {
                vec![#(#builder_fields,)*]
            }
        }

        impl #impl_generics From<Vec #ty_generics> for #iden #ty_generics {
            fn from(vec: Vec #ty_generics) -> #iden #ty_generics {
                assert!(vec.len() == #iden::#ty_generics::state_number());
                #iden {
                    #(#vec_to_fields,)*
                }               
            }
        }
    };
    expanded.into()
}


